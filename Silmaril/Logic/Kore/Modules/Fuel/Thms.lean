module

public import Silmaril.Proofs.Logic.Kore.Modules.Fuel.Sentences
public import Silmaril.Logic.Kore.Modules.Semantics.Thms

@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Checking

/-- Increasing fuel preserves exactly the successful typed result. -/
theorem elaborate_add (scope : Scope) (fuel extra : Nat) {k : Nat} {Γ : Fin k → String}
    (vs : List (Binding scope.signature Γ)) (s : String) (raw : RawPattern)
    (typed : FirstOrder.Pattern scope.signature Γ s)
    (accepted : elaborate scope fuel vs s raw = some typed) :
    elaborate scope (fuel + extra) vs s raw = some typed :=
  Silmaril.Proofs.Logic.Kore.Modules.Fuel.elaborate_add scope fuel extra vs s raw typed accepted

/-- The free-variable traversal preserves the same ordered list. -/
theorem freeVariables_add (fuel extra : Nat) (bound : List String) (raw : RawPattern)
    (names : List (String × String)) (accepted : freeVariables bound fuel raw = some names) :
    freeVariables bound (fuel + extra) raw = some names :=
  Silmaril.Proofs.Logic.Kore.Modules.Fuel.freeVariables_add fuel extra bound raw names accepted
/-- Any larger budget preserves success; no termination or acyclicity oracle is used. -/
theorem elaborate_mono (scope : Scope) {fuel larger : Nat} (budget : fuel ≤ larger)
    {k : Nat} {Γ : Fin k → String} (vs : List (Binding scope.signature Γ))
    (s : String) (raw : RawPattern) (typed : FirstOrder.Pattern scope.signature Γ s)
    (accepted : elaborate scope fuel vs s raw = some typed) :
    elaborate scope larger vs s raw = some typed := by
  simpa only [Nat.add_sub_of_le budget] using
    elaborate_add scope fuel (larger - fuel) vs s raw typed accepted

/-- Two successful budgets produce the same intrinsic pattern. -/
theorem elaborate_unique (scope : Scope) (fuel other : Nat) {k : Nat} {Γ : Fin k → String}
    (vs : List (Binding scope.signature Γ)) (s : String) (raw : RawPattern)
    (left right : FirstOrder.Pattern scope.signature Γ s)
    (hl : elaborate scope fuel vs s raw = some left)
    (hr : elaborate scope other vs s raw = some right) : left = right := by
  have l := elaborate_mono scope (Nat.le_max_left fuel other) vs s raw left hl
  have r := elaborate_mono scope (Nat.le_max_right fuel other) vs s raw right hr
  exact Option.some.inj (l.symm.trans r)

/-- Universal closure preserves the exact context, sort and body with more fuel. -/
theorem sentence_add (scope : Scope) (fuel extra : Nat) (raw : RawPattern)
    (typed : FirstOrder.Sentence scope.signature)
    (accepted : sentence scope fuel raw = some typed) :
    sentence scope (fuel + extra) raw = some typed :=
  Silmaril.Proofs.Logic.Kore.Modules.Fuel.sentence_add scope fuel extra raw typed accepted

theorem sentence_mono (scope : Scope) {fuel larger : Nat} (budget : fuel ≤ larger)
    (raw : RawPattern) (typed : FirstOrder.Sentence scope.signature)
    (accepted : sentence scope fuel raw = some typed) :
    sentence scope larger raw = some typed := by
  simpa only [Nat.add_sub_of_le budget] using
    sentence_add scope fuel (larger - fuel) raw typed accepted

theorem sentence_unique (scope : Scope) (fuel other : Nat) (raw : RawPattern)
    (left right : FirstOrder.Sentence scope.signature)
    (hl : sentence scope fuel raw = some left)
    (hr : sentence scope other raw = some right) : left = right := by
  have l := sentence_mono scope (Nat.le_max_left fuel other) raw left hl
  have r := sentence_mono scope (Nat.le_max_right fuel other) raw right hr
  exact Option.some.inj (l.symm.trans r)
end Silmaril.Logic.Kore.Modules.Checking

namespace Silmaril.Logic.Kore.Modules.Semantics
variable {scope : Scope} (M : Matching.FirstOrder.Model scope.signature)

/-- Accepted raw meaning is independent of additional fuel, in every environment
obtained by interpreting the arbitrary typed caller bindings. -/
theorem denote_add (fuel extra : Nat) {k : Nat} {Γ : Fin k → String}
    (vs : List (Checking.Binding scope.signature Γ))
    (v : (i : Fin k) → M.carrier (Γ i)) (s : String) (raw : RawPattern)
    (typed : FirstOrder.Pattern scope.signature Γ s)
    (accepted : Checking.elaborate scope fuel vs s raw = some typed) :
    denote M (fuel + extra) (interpret M vs v) s raw =
      denote M fuel (interpret M vs v) s raw := by
  rw [elaborate_sound M (fuel + extra) vs v s raw typed
    (Checking.elaborate_add scope fuel extra vs s raw typed accepted),
    elaborate_sound M fuel vs v s raw typed accepted]

/-- Independent raw validity is stable once the actual sentence checker accepts. -/
theorem satisfies_add (fuel extra : Nat) (raw : RawPattern)
    (typed : FirstOrder.Sentence scope.signature)
    (accepted : Checking.sentence scope fuel raw = some typed) :
    Satisfies M (fuel + extra) raw ↔ Satisfies M fuel raw :=
  (sentence_sound M (fuel + extra) raw typed
    (Checking.sentence_add scope fuel extra raw typed accepted)).trans
      (sentence_sound M fuel raw typed accepted).symm
theorem denote_mono {fuel larger : Nat} (budget : fuel ≤ larger)
    {k : Nat} {Γ : Fin k → String} (vs : List (Checking.Binding scope.signature Γ))
    (v : (i : Fin k) → M.carrier (Γ i)) (s : String) (raw : RawPattern)
    (typed : FirstOrder.Pattern scope.signature Γ s)
    (accepted : Checking.elaborate scope fuel vs s raw = some typed) :
    denote M larger (interpret M vs v) s raw = denote M fuel (interpret M vs v) s raw := by
  simpa only [Nat.add_sub_of_le budget] using
    denote_add M fuel (larger - fuel) vs v s raw typed accepted

theorem satisfies_mono {fuel larger : Nat} (budget : fuel ≤ larger)
    (raw : RawPattern) (typed : FirstOrder.Sentence scope.signature)
    (accepted : Checking.sentence scope fuel raw = some typed) :
    Satisfies M larger raw ↔ Satisfies M fuel raw := by
  simpa only [Nat.add_sub_of_le budget] using
    satisfies_add M fuel (larger - fuel) raw typed accepted
end Silmaril.Logic.Kore.Modules.Semantics
