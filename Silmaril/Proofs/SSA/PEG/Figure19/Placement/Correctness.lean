module

public import Silmaril.SSA.PEG.Figure19.Placement.Defs
public import Silmaril.SSA.PEG.Semantics.Thms

public section

namespace Silmaril.SSA.PEG.Figure19.Placement.Proofs

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results ins : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {depth : Fin l → Nat}
variable {direction : EvalDirection} {cap : Nat} {ctx : Assumptions n} {i target : Fin n}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params}
variable {values : g.Valuation m} {idx : Index l}

private theorem thetaDepth (typed : Derives g depth direction cap ctx i)
    {key : Fin l} {label : (g.node i).label.thetaLoop = some key} : depth key ≤ cap := by
  induction typed with
  | param row | op row _ _ | phi row _ _ _ _ _ _ | evalPass row _ _ _ _ _ _ _ =>
    have same := congrArg (fun node => node.label.thetaLoop) row
    rw [label] at same
    cases same
  | theta row _ _ _ _ _ | assume row _ =>
    have same := congrArg (fun node => node.label.thetaLoop) row
    rw [label] at same
    cases same
    exact Nat.le_refl _
  | reduce bound _ _ ih => exact Nat.le_trans (ih (label := label)) bound

private theorem opChild (typed : Derives g depth direction cap ctx i)
    {instr : P ins (g.sort i)} {args : Tuple (Ref g.sort) ins}
    (wired : g.node i = .ofLabel (.op instr) args) (slot : Fin ins.length) :
    Derives g depth direction cap ctx (args.get (portAt ins slot)).id := by
  induction typed with
  | param row | phi row _ _ _ _ _ _ | theta row _ _ _ _ _ | evalPass row _ _ _ _ _ _ _
  | assume row _ =>
    rw [wired] at row
    cases row
  | op row children _ =>
    rw [wired] at row
    cases row
    exact children slot
  | reduce bound subset _ ih => exact .reduce bound subset (ih wired)

theorem derives (path : StrictPath g target i) (typed : Derives g depth direction cap ctx i) :
    Derives g depth direction cap ctx target := by
  induction path with
  | here => exact typed
  | operand _ row slot _ ih => exact ih (opChild typed row slot)

theorem depth_le (path : StrictPath g target i) (typed : Derives g depth direction cap ctx i)
    {key : Fin l} (theta : (g.node target).label.thetaLoop = some key) : depth key ≤ cap :=
  thetaDepth (label := theta) (derives path typed)

theorem phiArms (typed : Derives g depth direction cap ctx i)
    {flag : Ref g.sort .bool} {yes no : Ref g.sort (g.sort i)}
    (wired : g.node i = .ofLabel .phi (.cons flag (.cons yes (.cons no .nil)))) :
    Derives g depth direction cap ctx yes.id ∧ Derives g depth direction cap ctx no.id := by
  induction typed with
  | param row | op row _ _ | theta row _ _ _ _ _ | evalPass row _ _ _ _ _ _ _
  | assume row _ =>
    have labels := congrArg (fun node => match node with
      | ⟨_, .phi, _⟩ => true
      | _ => false) (wired.symm.trans row)
    cases labels
  | phi row _ yes no _ _ _ =>
    rw [wired] at row
    cases row
    exact ⟨yes, no⟩
  | reduce bound subset _ ih =>
    obtain ⟨yes, no⟩ := ih wired
    exact ⟨.reduce bound subset yes, .reduce bound subset no⟩

private theorem collectRead {read : ∀ slot : Fin ins.length, Option (m.Value ins[slot])}
    {xs : Tuple m.Value ins} (h : collect ins read = some xs) (slot : Fin ins.length) :
    (read slot).isSome := by
  induction ins with
  | nil => exact slot.elim0
  | cons t ts ih =>
    cases ha : read 0 with
    | none => simp [collect, ha] at h
    | some x =>
      cases hb : collect ts (fun s => read s.succ) with
      | none => simp [collect, ha, hb] at h
      | some ys => exact Fin.cases (by rw [ha]; rfl) (fun j => ih hb j) slot

private theorem refDefined {t : Ty Data} (ref : Ref g.sort t) :
    (ref.read m.carrier (values (ref.id, idx))).isSome = (values (ref.id, idx)).isSome := by
  obtain ⟨child, typed⟩ := ref
  subst t
  rfl

theorem defined (path : StrictPath g target i) (solves : g.Solves m env values)
    (start : (values (i, idx)).isSome) : (values (target, idx)).isSome := by
  induction path with
  | here => exact start
  | @operand i ins instr args row slot rest ih =>
    apply ih
    rw [solves (i, idx)] at start
    change (let node := g.node i; node.label.interpret m env idx fun slot j _ =>
      (node.arg slot).read m.carrier (values ((node.arg slot).id, j))).isSome at start
    rw [row] at start
    let read (j : Fin ins.length) :=
      let arg := args.get (portAt ins j)
      arg.read m.carrier (values (arg.id, idx))
    change ((collect ins read).elim none (m.run instr)).isSome at start
    cases h : collect ins read with
    | none => simp [h] at start
    | some vals =>
      have hit := collectRead h slot
      dsimp only [read] at hit
      exact (refDefined _).symm ▸ hit

theorem phi_demands {args : Tuple (Ref g.sort) [.bool, g.sort i, g.sort i]}
    (row : g.node i = .ofLabel .phi args)
    (solves : g.Solves m env values) (start : (values (i, idx)).isSome) :
    (values ((args.get .head).id, idx)).isSome ∧
      ((values ((args.get (.tail .head)).id, idx)).isSome ∨
       (values ((args.get (.tail (.tail .head))).id, idx)).isSome) := by
  let flag := args.get .head
  let yes := args.get (.tail .head)
  let no := args.get (.tail (.tail .head))
  rw [solves (i, idx)] at start
  change (let node := g.node i; node.label.interpret m env idx fun slot j _ =>
    (node.arg slot).read m.carrier (values ((node.arg slot).id, j))).isSome at start
  rw [row] at start
  let read {t} (ref : Ref g.sort t) := ref.read m.carrier (values (ref.id, idx))
  change ((read flag).elim none (fun b => if b.down then read yes else read no)).isSome at start
  cases h : read flag with
  | none => simp [h] at start
  | some b =>
    have flagDefined : (values (flag.id, idx)).isSome := by
      rw [← refDefined flag]
      change (read flag).isSome
      rw [h]
      rfl
    rw [h, Option.elim] at start
    refine ⟨flagDefined, ?_⟩
    split at start
    · exact .inl ((refDefined yes).symm ▸ start)
    · exact .inr ((refDefined no).symm ▸ start)

theorem defined_of_phi {flag : Ref g.sort .bool} {yes no : Ref g.sort (g.sort i)}
    (row : g.node i = .ofLabel .phi (.cons flag (.cons yes (.cons no .nil))))
    (trueUse : StrictPath g target yes.id) (falseUse : StrictPath g target no.id)
    (solves : g.Solves m env values) (start : (values (i, idx)).isSome) :
    (values (target, idx)).isSome :=
  (phi_demands row solves start).2.elim (defined trueUse solves) (defined falseUse solves)

end Silmaril.SSA.PEG.Figure19.Placement.Proofs
