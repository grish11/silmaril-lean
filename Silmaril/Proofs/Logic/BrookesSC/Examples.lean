module

public import Silmaril.Logic.BrookesSC.Thms
import Mathlib.Data.Set.Lattice.Order
import Mathlib.Logic.Function.Basic

/-! Finite state observations of explicitly ordered primitive requests. -/

@[expose] public section

namespace Silmaril.Logic.BrookesSC.Examples

open CategoryTheory

abbrev value : Bool → Type
  | false => Nat
  | true => Bool

abbrev world : World := ⟨Bool, Bool, value, Unit, Unit, fun _ => Bool⟩

structure State where
  memory : (c : Bool) → value c
  owner : Option Bool

def step (p : Primitive world) (st : State) : Option (p.Reply × State) :=
  match p with
  | .load _ _ cell => some (st.memory cell, st)
  | .store _ _ cell v => some (⟨⟩, {st with memory := Function.update st.memory cell v})
  | .acquire thread _ => if st.owner = none then some (⟨⟩, {st with owner := some thread}) else none
  | .release thread _ => if st.owner = some thread then some (⟨⟩, {st with owner := none}) else none

/-- May outcomes of a specified finite order, observing the result and final state.
A disabled mutex step has no successful outcome. -/
def stateTarget : Target world where
  Carrier A := State → Set (A × State)
  order _ := inferInstance
  pure a st := {out | out = (a, st)}
  bind x k st := {out | ∃ mid ∈ x st, out ∈ k mid.1 mid.2}
  primitive p st := {out | step p st = some out}
  bind_mono hx hk st out := by
    rintro ⟨mid, hmid, hout⟩
    exact ⟨mid, hx st hmid, hk mid.1 mid.2 hout⟩

abbrev source : Signature world := ⟨fun _ => Unit⟩
abbrev extended : Signature world := ⟨fun _ => Bool⟩

/-- The source label selects the true-labelled copy of each operation. -/
def inclusion : source ⟶ extended := ⟨fun _ => true⟩

/-- Swap the two spellings of every operation. -/
def swap : extended ⟶ extended := ⟨Bool.not⟩

def model : Model stateTarget extended :=
  ⟨fun label st => {out | out = (label, st)}⟩

def both : Model stateTarget extended :=
  ⟨fun _ st => {out | out.2 = st}⟩

/-- The label-sensitive model has strictly fewer behaviors than `both`. -/
def modelArrow : model ⟶ both :=
  ⟨fun {_} _ _ _ hout => show _ from (congrArg Prod.snd hout)⟩

abbrev put (n : Nat) : Designation world := .primitive (.store false .scAtomic false n)
abbrev get : Designation world := .primitive (.load false .scAtomic false)
abbrev ask : Designation world := .external ()

/-- The left side writes its open input, reads it and branches on an external reply.
The right side writes the same input and returns it immediately. -/
abbrev readBack : Sentence source where
  Input := Nat
  Result := Nat
  lhs n := .call (d := put n) () fun _ =>
    .call (d := get) () fun (observed : Nat) =>
      .call (d := ask) () fun (yes : Bool) => .ret (if yes then observed else observed + 1)
  rhs n := .call (d := put n) () fun _ => .ret n

private def afterWrite (st : State) (n : Nat) : State :=
  { st with memory := Function.update st.memory false n }

private theorem lhs_outcomes (label : Bool) (n : Nat) (st : State) :
    (model.eval ((readBack.lhs n).translate (⟨fun _ => label⟩ : source ⟶ extended))) st =
      {(if label then n else n + 1, afterWrite st n)} := by
  ext out
  simp [readBack, Program.translate, Model.eval, Model.operation, model, stateTarget, step, put, get,
    ask, afterWrite, Set.mem_singleton_iff, Function.update_self]

private theorem rhs_outcomes (f : source ⟶ extended) (n : Nat) (st : State) :
    (model.eval ((readBack.rhs n).translate f)) st = {(n, afterWrite st n)} := by
  ext out
  simp [readBack, Program.translate, Model.eval, Model.operation, stateTarget, step, put,
    afterWrite, Set.mem_singleton_iff]

theorem translated_readBack : (readBack.translate inclusion).Satisfies model := by
  intro n st
  change Nat at n
  change model.eval ((readBack.lhs n).translate inclusion) st ⊆
    model.eval ((readBack.rhs n).translate inclusion) st
  rw [show inclusion = (⟨fun _ => true⟩ : source ⟶ extended) from rfl,
    lhs_outcomes true n st, rhs_outcomes]
  exact Set.Subset.rfl

theorem reduct_readBack : readBack.Satisfies (model.reduct inclusion) :=
  (Institution.satisfaction_condition (institution stateTarget) inclusion model readBack).mp
    translated_readBack

/-- The same sentence changes truth when a nonidentity map selects the other
external operation, whose reply differs in this model. -/
theorem swapped_readBack_fails : ¬ (readBack.translate (inclusion ≫ swap)).Satisfies model := by
  intro h
  let initial : State := ⟨fun | false => (0 : Nat) | true => false, none⟩
  have h₀ : model.eval ((readBack.lhs 0).translate (inclusion ≫ swap)) initial ⊆
      model.eval ((readBack.rhs 0).translate (inclusion ≫ swap)) initial := h (0 : Nat) initial
  rw [show inclusion ≫ swap = (⟨fun _ => false⟩ : source ⟶ extended) from rfl,
    lhs_outcomes false 0 initial, rhs_outcomes] at h₀
  have bad := h₀ (Set.mem_singleton (1, afterWrite initial 0))
  simp at bad

def locked : State := ⟨fun | false => (0 : Nat) | true => false, some false⟩

theorem noReverseModelArrow : ¬ Nonempty (both ⟶ model) := by
  rintro ⟨h⟩
  have bad : (false, locked) = (true, locked) := h.down (s := ()) true locked (a := (false, locked)) rfl
  cases congrArg Prod.fst bad

/-- The other thread cannot acquire an owned mutex or release it. After the
owner releases it, the other thread can acquire it. -/
theorem mutex_order :
    step (.acquire true ()) locked = none ∧
    step (.release true ()) locked = none ∧
    (step (.release false ()) locked).bind (fun out => step (.acquire true ()) out.2) =
      some (⟨⟩, {locked with owner := some true}) := by
  exact ⟨rfl, rfl, rfl⟩

end Silmaril.Logic.BrookesSC.Examples
