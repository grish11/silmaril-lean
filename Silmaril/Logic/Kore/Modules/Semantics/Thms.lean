module

public import Silmaril.Logic.Kore.Modules.Semantics.Defs
public import Silmaril.Proofs.Logic.Kore.Modules.Semantics.Sentences

@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Semantics
variable {scope : Scope} (M : Matching.FirstOrder.Model scope.signature)

/-- Arbitrary-pattern source adequacy, including named binders, arbitrary-arity
operations and recursively unfolded aliases with arbitrary caller patterns. -/
theorem elaborate_sound (fuel : Nat) {k : Nat} {Γ : Fin k → String}
    (vs : List (Checking.Binding scope.signature Γ))
    (v : (i : Fin k) → M.carrier (Γ i)) (s : String) (raw : RawPattern)
    (typed : FirstOrder.Pattern scope.signature Γ s)
    (accepted : Checking.elaborate scope fuel vs s raw = some typed) :
    denote M fuel (interpret M vs v) s raw = FirstOrder.denote scope.signature M v typed :=
  Silmaril.Proofs.Logic.Kore.Modules.Semantics.elaborate_sound M fuel vs v s raw typed accepted

theorem sentence_sound (fuel : Nat) (raw : RawPattern)
    (typed : FirstOrder.Sentence scope.signature)
    (accepted : Checking.sentence scope fuel raw = some typed) :
    Satisfies M fuel raw ↔ FirstOrder.Sentence.Satisfies M typed :=
  Silmaril.Proofs.Logic.Kore.Modules.Semantics.sentence_sound M fuel raw typed accepted
end Silmaril.Logic.Kore.Modules.Semantics
