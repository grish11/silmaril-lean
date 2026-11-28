module

public import Silmaril.Logic.BrookesSC.Concrete.Observation.Thms

/-! Checked fixtures for the public concrete institution and singleton observation. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.BrookesSC.Concrete.Regression

open CategoryTheory Silmaril.Logic.BrookesSC Silmaril.Logic.BrookesSC.Concrete
open Silmaril.Logic.BrookesSC.Concrete.Observation Silmaril.Semantics.Brookes

abbrev CellValue : Bool → Type
  | false => Nat
  | true => Bool

abbrev world : World := ⟨Bool, Bool, CellValue, Bool, Unit, fun _ => Bool⟩

abbrev source : Signature world := ⟨fun _ => Unit⟩
abbrev destination : Signature world := ⟨fun _ => Bool⟩

def select (label : Bool) : source ⟶ destination := ⟨fun _ => label⟩

def replies (flip : Bool) : TraceModel destination :=
  ⟨fun label => Behavior.ret (if flip then !label else label)⟩

def initial : Store world :=
  ⟨fun | false => (0 : Nat) | true => false, fun _ => none⟩

abbrev ask : Designation world := .external ()

abbrev branch : Sentence source where
  Input := Nat
  Result := Nat
  lhs n := .call (d := ask) () fun answer => .ret (if answer then n else n + 1)
  rhs n := .ret n

private theorem translated_eval (flip label : Bool) (n : Nat) :
    (replies flip).eval ((branch.lhs n).translate (select label)) =
      Behavior.ret (if (if flip then !label else label) then n else n + 1) := by
  rw [show (branch.lhs n).translate (select label) =
    .call (d := ask) label (fun answer => .ret (if answer then n else n + 1)) from
      Program.translate.eq_2 .., eval_call_external (replies flip) (sort := ())]
  change (Behavior.ret (if flip then !label else label)).bind _ = _
  rw [Behavior.ret_bind, eval_ret (replies flip)]

theorem translated_branch : (branch.translate (select true)).Satisfies (replies false) := by
  rw [satisfies_iff (replies false)]
  intro n
  change Nat at n
  change Includes ((replies false).eval ((branch.lhs n).translate (select true)))
    ((replies false).eval ((branch.rhs n).translate (select true)))
  rw [translated_eval, show (branch.rhs n).translate (select true) = .ret n from
    Program.translate.eq_1 .., eval_ret (replies false)]
  intro _ _ h
  exact h

theorem reduct_branch : branch.Satisfies ((replies false).reduct (select true)) :=
  (Silmaril.Logic.Institution.satisfaction_condition
    (Silmaril.Logic.BrookesSC.Concrete.institution world) (select true) (replies false) branch).mp
    translated_branch

/-- The same translated sentence fails when the target model flips the reply. -/
theorem translated_branch_fails : ¬ (branch.translate (select true)).Satisfies (replies true) := by
  rw [satisfies_iff (replies true)]
  intro h
  have includes : Includes ((replies true).eval ((branch.lhs 0).translate (select true)))
      ((replies true).eval ((branch.rhs 0).translate (select true))) := h (0 : Nat)
  rw [translated_eval, show (branch.rhs 0).translate (select true) = .ret 0 from
    Program.translate.eq_1 .., eval_ret (replies true)] at includes
  have one : (Behavior.ret (1 : Nat) : Behavior (Store world) Nat).accepts [(initial, initial)] 1 :=
    Behavior.ret_accepts_iff.mpr ⟨initial, rfl, .refl _⟩
  have zero : (Behavior.ret (0 : Nat) : Behavior (Store world) Nat).accepts [(initial, initial)] 1 :=
    includes one
  obtain ⟨_, bad, _⟩ := Behavior.ret_accepts_iff.mp zero
  cases bad

theorem reduct_branch_fails : ¬ branch.Satisfies ((replies true).reduct (select true)) :=
  fun h => translated_branch_fails ((satisfaction (select true) (replies true) branch).mpr h)

abbrev put : Primitive world := .store false .scAtomic false 0
abbrev get : Primitive world := .load false .plain false

abbrev readBack : Sentence source where
  Input := Unit
  Result := Nat
  lhs _ := .call (d := .primitive put) () fun _ => .call (d := .primitive get) () Program.ret
  rhs _ := .call (d := .primitive put) () fun _ => .ret 0

private def wrote (s : Store world) : Store world :=
  {s with memory := Function.update s.memory false 0}

private theorem readBack_lhs (m : TraceModel source) :
    m.eval (readBack.lhs ()) = (primitive put).bind (fun _ => primitive get) := by
  change m.eval (.call (d := .primitive put) () fun _ =>
    .call (d := .primitive get) () Program.ret) = _
  rw [eval_call_primitive m (p := put)]
  congr 1
  funext _
  exact eval_call_primitive_ret m (p := get) ()

private theorem readBack_rhs (m : TraceModel source) :
    m.eval (readBack.rhs ()) = (primitive put).bind (fun _ => Behavior.ret 0) := by
  change m.eval (.call (d := .primitive put) () fun _ => .ret 0) = _
  rw [eval_call_primitive m (p := put)]
  congr 1

/-- The write/read-back inequation holds on single-store observations. -/
theorem readBack_state (m : TraceModel source) : readBack.Satisfies (observeModel m) := by
  intro input s t r h
  cases input
  change (observeModel m).eval (readBack.lhs ()) s t r at h
  change (observeModel m).eval (readBack.rhs ()) s t r
  rw [← observe_eval m, readBack_lhs, observe_bind_iff] at h
  rw [← observe_eval m, readBack_rhs, observe_bind_iff]
  obtain ⟨mid, reply, hp, hg⟩ := h
  have hp' : some (⟨⟩, wrote s) = some (reply, mid) := (primitive_completes_iff put ..).mp hp
  have hg' : some (mid.memory false, mid) = some (r, t) := (primitive_completes_iff get ..).mp hg
  obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj hp')
  obtain ⟨hr, ht⟩ := Prod.mk.inj (Option.some.inj hg')
  exact ⟨wrote s, reply, hp, (observe_ret_iff ..).mpr ⟨ht, hr.symm.trans (by rfl)⟩⟩

/-- An environment write between program segments can change the observed reply. -/
theorem readBack_trace_fails (m : TraceModel source) : ¬ readBack.Satisfies m := by
  let changed : Store world := {initial with memory := Function.update initial.memory false 1}
  let trace : Trace (Store world) := [(initial, wrote initial), (changed, changed)]
  have left : (m.eval (readBack.lhs ())).accepts trace 1 := by
    rw [readBack_lhs]
    exact Behavior.bind_accepts_iff.mpr ⟨[(initial, wrote initial)], [(changed, changed)], ⟨⟩,
      (primitive_completes_iff put ..).mpr rfl, (primitive_completes_iff get ..).mpr rfl, .refl _⟩
  intro h
  have right : (m.eval (readBack.rhs ())).accepts trace 1 := (satisfies_iff m readBack).mp h () left
  rw [readBack_rhs] at right
  obtain ⟨_, _, _, _, hr, _⟩ := Behavior.bind_accepts_iff.mp right
  obtain ⟨_, bad, _⟩ := Behavior.ret_accepts_iff.mp hr
  cases bad

def held : Store world := {initial with owner := fun _ => some false}
def unlocked : Store world := {held with owner := Function.update held.owner false none}
def heldByOther : Store world := {unlocked with owner := Function.update unlocked.owner false (some true)}

theorem release_acquire_guards :
    ¬ (primitive (.release true false : Primitive world)).completes held unlocked ⟨⟩ ∧
    (primitive (.release false false : Primitive world)).completes held unlocked ⟨⟩ ∧
    ¬ (primitive (.acquire false false : Primitive world)).completes held held ⟨⟩ ∧
    (primitive (.acquire true false : Primitive world)).completes unlocked heldByOther ⟨⟩ := by
  simp only [primitive_completes_iff (W := world)]
  exact ⟨nofun, rfl, nofun, rfl⟩

/-- A held mutex can stutter before an environment release and a legal acquire. -/
theorem acquire_after_gap :
    (primitive (.acquire true false : Primitive world)).accepts
      [(held, held), (unlocked, heldByOther)] ⟨⟩ := by
  exact (primitive_accepts_iff (.acquire true false : Primitive world) ..).mpr
    ⟨unlocked, heldByOther, rfl,
      .tail (.refl _) (Rewrite.stutter [] [(unlocked, heldByOther)] held)⟩

theorem no_step_no_trace (trace : Trace (Store world)) :
    ¬ (Behavior.atomic (fun (_ _ : Store world) (_ : Unit) => False)).accepts trace () := by
  rintro mem
  obtain ⟨_, _, impossible, _⟩ := Behavior.atomic_accepts_iff.mp mem
  exact impossible

end Silmaril.Proofs.Logic.BrookesSC.Concrete.Regression
