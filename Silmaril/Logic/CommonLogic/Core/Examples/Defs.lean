module

public import Silmaril.Logic.CommonLogic.Core.Defs

@[expose] public section

namespace Silmaril.Logic.CommonLogic.Core.Examples

/-- Two individual names, one genuinely non-discourse name, and a sequence marker. -/
def signature : Signature := ⟨Bool, Unit, Unit⟩

/-- Reference values include one extra object outside the entire natural-number discourse.
Individual 0 acts as equality-of-all-arguments predicate; individual 1 as nonempty predicate.
The non-discourse reference acts as an always-false predicate. Functions return argument length. -/
def model : Model signature where
  Reference := Option Nat
  Discourse := Nat
  nonempty := ⟨0⟩
  embed := some
  injective := fun _ _ h => Option.some.inj h
  discourse := fun (b : Bool) => if b then 1 else 0
  nondiscourse _ := none
  outside _ _ := by intro h; cases h
  sequence _ := [2,3]
  function _ xs := xs.length
  relation r xs := match r with
    | none => False
    | some 0 => ∀ x ∈ xs, x = 2
    | some _ => xs ≠ []

/-- A quantified individual occurs both as predicate head and its own argument. -/
def higherPredicate : Sentence signature :=
  .ex (.pred (.lift (.var 0)) (.cons (.var 0) .nil))

/-- A quantified sequence is spliced between two ordinary arguments. -/
def sequenceWitness : Sentence signature :=
  .exSeq (.equal (.app (.lift (.name true))
    (.cons (.name false) (.append (.seqvar 0) (.cons (.name true) .nil))))
    (.app (.lift (.name false)) (.append (.marker ()) (.marker ()))))

/-- Universal sequence quantification includes the empty list. -/
def everySequenceNonempty : Sentence signature :=
  .allSeq (.pred (.lift (.name true)) (.seqvar 0))

/-- Arbitrary function applications can themselves be predicate heads. -/
def computedHead : Sentence signature :=
  .pred (.lift (.app (.nonname ()) (.cons (.name false) .nil)))
    (.cons (.name true) .nil)

/-- Bare name false denotes 0, but applying that same object to [] returns 0;
name true denotes 1, whereas its nullary application returns 0. -/
def nameNotNullary : Sentence signature :=
  .neg (.equal (.name true) (.app (.lift (.name true)) .nil))

/-- A non-injective symbol map identifies both discourse names, preserving symbol classes. -/
def collapse : Signature.Hom signature signature := ⟨fun _ => false, id, id⟩

end Silmaril.Logic.CommonLogic.Core.Examples
