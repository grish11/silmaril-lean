module

public import Silmaril.Logic.CommonLogic.ManySorted.Expansion.Thms

/-! Boundary examples for empty carriers, nullary symbols and off-profile arguments. -/
@[expose] public section
noncomputable section

namespace Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic Silmaril.Logic.CommonLogic.ManySorted
open Silmaril.Logic.CommonLogic.ManySorted.Expansion

def emptySignature (Sorts : Type) : FOL.Signature :=
  ⟨⟨Sorts, fun _ _ _ => Empty⟩, fun _ _ => Empty⟩

def emptySource (Sorts : Type) : FOL.Structure (emptySignature Sorts) where
  carrier := fun _ => Empty
  op o := Empty.elim o
  rel r := Empty.elim r

/-- An empty sort set still expands to an inhabited CL discourse. -/
theorem no_sorts_only_junk (x : Discourse (emptySource Empty)) :
    x = junk (emptySource Empty) := by
  rcases x with u | ⟨s, a⟩
  · cases u
    rfl
  · exact Empty.elim s

/-- No source inhabitant is introduced by the extra CL junk value. -/
theorem decoded_empty_carrier (Sorts : Type) (s : Sorts) :
    IsEmpty ((decode (expand (emptySource Sorts))).carrier s) :=
  ⟨fun x => Empty.elim (unpack (emptySource Sorts) x)⟩

theorem empty_source_recovered (Sorts : Type) :
    Nonempty (decode (expand (emptySource Sorts)) ≅ emptySource Sorts) :=
  ⟨decodeExpandIso (emptySource Sorts)⟩

/-- The test source has a symbol at every operation/relation profile. -/
def numericSignature : FOL.Signature :=
  ⟨⟨Unit, fun _ _ _ => Unit⟩, fun _ _ => Unit⟩

def numericSource : FOL.Structure numericSignature where
  carrier := fun _ => Nat
  op := fun _ _ => 7
  rel := fun _ args => ∀ i, args i = 7

/-- Nullary application yields its tagged source value, not junk. -/
theorem nullary_value {w : Fin 0 → numericSignature.S} (o : numericSignature.Op 0 w ()) :
    (raw numericSource).function
      ((raw numericSource).nondiscourse (.op (n := 0) (w := w) (s := ()) o)) [] =
      tag numericSource () (7 : Nat) := by
  have h :=
    function_encode numericSource (n := 0) (w := w) (s := ()) o (fun i => i.elim0)
  have hempty : encode numericSource (w := w) (fun i => i.elim0) = [] :=
    List.ofFn_zero
  rw [hempty] at h
  exact h

/-- All well-sorted source argument lists preserve their function interpretation. -/
theorem tagged_function {n : Nat} {w : Fin n → numericSignature.S}
    (o : numericSignature.Op n w ()) (args : ∀ i, numericSource.carrier (w i)) :
    (raw numericSource).function ((raw numericSource).nondiscourse (.op o))
      (encode numericSource args) = tag numericSource () (7 : Nat) :=
  function_encode numericSource o args

/-- Tagged relation tuples retain the source predicate, including arity zero. -/
theorem tagged_relation {n : Nat} {w : Fin n → numericSignature.S}
    (r : numericSignature.Rel n w) (args : ∀ i, numericSource.carrier (w i)) :
    (raw numericSource).relation ((raw numericSource).nondiscourse (.rel r))
      (encode numericSource args) ↔ ∀ i, args i = (7 : Nat) :=
  relation_encode numericSource r args

/-- A junk argument is rejected by a unary operation's sorted tuple decoder. -/
theorem off_profile_function (o : numericSignature.Op 1 (fun _ => ()) ()) :
    (raw numericSource).function ((raw numericSource).nondiscourse (.op o))
      [junk numericSource] = junk numericSource := by
  apply function_off_profile
  rintro ⟨args, h⟩
  simp only [encode, List.ofFn_succ, List.ofFn_zero] at h
  have bad : junk numericSource = tag numericSource () (args 0) :=
    List.singleton_inj.mp h
  cases bad

/-- Sort predicates never contain junk, even if some source sort is inhabited. -/
theorem junk_not_sorted {S : FOL.Signature} (M : FOL.Structure S) (s : S.S) :
    ¬ (raw M).relation ((raw M).nondiscourse (.sort s)) [junk M] := by
  rintro ⟨a, h⟩
  have bad : junk M = tag M s a := List.singleton_inj.mp h
  cases bad

/-- Outside the recognized tagged relation tuples, the relation is false. -/
theorem off_profile_relation (r : numericSignature.Rel 1 (fun _ => ())) :
    ¬ (raw numericSource).relation ((raw numericSource).nondiscourse (.rel r))
      [junk numericSource] := by
  rintro ⟨args, h, hr⟩
  simp only [encode, List.ofFn_succ, List.ofFn_zero] at h
  have bad : junk numericSource = tag numericSource () (args 0) :=
    List.singleton_inj.mp h
  cases bad

end Silmaril.Logic.CommonLogic.ManySorted.Expansion.Examples
