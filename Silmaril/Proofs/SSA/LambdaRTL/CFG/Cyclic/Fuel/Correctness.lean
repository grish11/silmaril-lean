module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Fuel.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Thms
public import Silmaril.Semantics.Elgot.Thms

public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Fuel.Proofs

universe v w

set_option backward.isDefEq.respectTransparency false

variable {V K α R : Type w} {F : Type v}
variable (m : Model F Option α)

private theorem ofOption_bind {A B : Type w} (x : Option A) (f : A → Option B) :
    Part.ofOption (x.bind f) = (Part.ofOption x).bind (fun a => Part.ofOption (f a)) := by
  cases x with
  | none => exact (Part.bind_none _).symm
  | some a => exact (Part.bind_some a (fun value => Part.ofOption (f value))).symm

private theorem val_eval (v : Val V) (store : V → α) :
    v.eval (toPartModel m) store = v.eval m store := by
  induction v with
  | var => rfl
  | unit => rfl
  | pair _ _ l r => exact congrArg₂ m.pair l r

private theorem op_eval (op : Op V F) (store : V → α) :
    op.eval (toPartModel m) store = Part.ofOption (op.eval m store) := by
  cases op <;> simp only [Op.eval, val_eval] <;> rfl

variable [DecidableEq V]

private theorem term_exec (next : K → α → (V → α) → Option R)
    (term : Term V K F) (store : V → α) :
    term.exec (toPartModel m) (fun label arg σ => Part.ofOption (next label arg σ)) store =
      Part.ofOption (term.exec m next store) := by
  induction term generalizing store with
  | br => simp only [Term.exec, val_eval]
  | case op x left y right ihLeft ihRight =>
    have split : (toPartModel m).split = fun a => Part.ofOption (m.split a) := rfl
    simp only [Term.exec, op_eval, Part.bind_eq_bind, Option.bind_eq_bind, split, ← ofOption_bind]
    let first := (op.eval m store).bind m.split
    let branch : α ⊕ α → Option R
      | .inl a => left.exec m next (upd store x a)
      | .inr a => right.exec m next (upd store y a)
    change (Part.ofOption first).bind _ = Part.ofOption (first.bind branch)
    rw [ofOption_bind first branch]
    refine congrArg (Part.ofOption first).bind ?_
    funext choice
    cases choice with
    | inl a => exact ihLeft (upd store x a)
    | inr a => exact ihRight (upd store y a)

private theorem body_exec (next : K → α → (V → α) → Option R)
    (body : Body V K F) (store : V → α) :
    body.exec (toPartModel m) (fun label arg σ => Part.ofOption (next label arg σ)) store =
      Part.ofOption (body.exec m next store) := by
  induction body generalizing store with
  | term term => exact term_exec m next term store
  | let1 x op tail ih =>
    simp only [Body.exec, op_eval, Part.bind_eq_bind, Option.bind_eq_bind, ih, ← ofOption_bind]
  | let2 x y op tail ih =>
    have unpair : (toPartModel m).unpair = fun a => Part.ofOption (m.unpair a) := rfl
    simp only [Body.exec, op_eval, Part.bind_eq_bind, Option.bind_eq_bind, unpair, ih, ← ofOption_bind]

variable [DecidableEq K]

private theorem step_toPart (table : List (K × Block V K F)) (start : Transfer V K α) :
    step (toPartModel m) table start = Part.ofOption (step m table start) := by
  unfold step
  split
  · rfl
  · rename_i block _
    exact body_exec m (fun label packet store =>
      some (Sum.inr (α := Transfer V K α) (label, packet, store))) block.body _

private theorem runs_iff_fuel (table : List (K × Block V K F)) (start output : Transfer V K α) :
    Silmaril.Elgot.Part.Runs (step (toPartModel m) table) start output ↔
      ∃ fuel, runFromFuel m table fuel start = some output := by
  constructor
  · intro ran
    induction ran with
    | @done current result done =>
      have stepRan := Part.mem_ofOption.mp (step_toPart m table current ▸ done)
      exact ⟨1, by rw [runFromFuel, stepRan]⟩
    | @more current next result more tail ih =>
      obtain ⟨fuel, rest⟩ := ih
      have stepRan := Part.mem_ofOption.mp (step_toPart m table current ▸ more)
      exact ⟨fuel + 1, by rw [runFromFuel, stepRan]; exact rest⟩
  · rintro ⟨fuel, ran⟩
    induction fuel generalizing start with
    | zero => cases ran
    | succ fuel ih =>
      rw [runFromFuel] at ran
      cases stepped : step m table start with
      | none => rw [stepped] at ran; cases ran
      | some choice =>
        rw [stepped] at ran
        have member : choice ∈ step (toPartModel m) table start :=
          (step_toPart m table start).symm ▸ Part.mem_ofOption.mpr stepped
        cases choice with
        | inl result =>
          have same : result = output := Option.some.inj ran
          exact same ▸ Silmaril.Elgot.Part.Runs.done member
        | inr next => exact .more member (ih next ran)

theorem mem_run_iff (cfg : CFG V K F) (store : V → α) (output : Transfer V K α) :
    output ∈ Cyclic.run (toPartModel m) cfg store ↔ ∃ fuel, runFuel m cfg fuel store = some output := by
  let enter := cfg.entry.exec m (fun label arg σ => some (label, arg, σ)) store
  let next := Silmaril.Elgot.iter (step (toPartModel m) cfg.blocks)
  have run : Cyclic.run (toPartModel m) cfg store = Part.ofOption enter >>= next := by
    rw [Cyclic.run, ← body_exec m]
    simp only [Body.exec_eq_evalRTL, Part.bind_eq_bind, Part.bind_assoc, Part.ofOption, Part.bind_some, next]
  rw [run, Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · rintro ⟨initial, entered, returned⟩
    obtain ⟨fuel, ran⟩ := (runs_iff_fuel m cfg.blocks initial output).mp
      ((Silmaril.Elgot.Part.mem_iter_iff _ _ _).mp returned)
    exact ⟨fuel, Option.bind_eq_some_iff.mpr ⟨initial, Part.mem_ofOption.mp entered, ran⟩⟩
  · rintro ⟨fuel, ran⟩
    obtain ⟨initial, entered, rest⟩ := Option.bind_eq_some_iff.mp ran
    exact ⟨initial, Part.mem_ofOption.mpr entered,
      (Silmaril.Elgot.Part.mem_iter_iff _ _ _).mpr ((runs_iff_fuel m cfg.blocks initial output).mpr ⟨fuel, rest⟩)⟩

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Fuel.Proofs
