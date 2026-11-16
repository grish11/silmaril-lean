module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Source

set_option linter.concreteInstances false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Silmaril.Logic.Kore.GeneralFixedPoint
open Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
open Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
variable [SortBindings]
variable {scope : Silmaril.Logic.Kore.Modules.Scope}
variable {M : Silmaril.Logic.Matching.GeneralFixedPoint.Model scope.signature}

/-- Actual finite raw environments may bind empty and nonsingleton object sets.
The only premise is existence of the referenced binding at its exact sort. -/
theorem source_variable (B : Carriers M) (objects : Builtins.Semantics.Values M)
    (s : ValueSort) (name : String) (fuel : Nat)
    (declared : Silmaril.Logic.Kore.Modules.Checking.namedSort scope s.name = true)
    (legal : (Builtins.Semantics.lookupValue M objects name s.name).isSome = true) :
    Builtins.Semantics.denote scope [] M B (fuel + 1) [] objects s.name (.evar name s.name) =
      some {x | sourceEquiv B s x ∈
        (Pattern.variable s name).denote (sourceValuation B objects)} := by
  simp only [Builtins.Semantics.denote, ne_eq, not_true_eq_false, declared, Bool.not_true]
  cases found : Builtins.Semantics.lookupValue M objects name s.name with
  | none => simp [found] at legal
  | some X =>
      apply congrArg some
      ext x
      simp [Pattern.denote, sourceValuation, found]

theorem source_top (B : Carriers M) (objects : Builtins.Semantics.Values M)
    (s : ValueSort) (fuel : Nat)
    (declared : Silmaril.Logic.Kore.Modules.Checking.namedSort scope s.name = true) :
    Builtins.Semantics.denote scope [] M B (fuel + 1) [] objects s.name (.top s.name) =
      some {x | sourceEquiv B s x ∈
        (Pattern.top s).denote (sourceValuation B objects)} := by
  simp [Builtins.Semantics.denote, declared, Pattern.denote]

theorem source_bottom (B : Carriers M) (objects : Builtins.Semantics.Values M)
    (s : ValueSort) (fuel : Nat)
    (declared : Silmaril.Logic.Kore.Modules.Checking.namedSort scope s.name = true) :
    Builtins.Semantics.denote scope [] M B (fuel + 1) [] objects s.name (.bottom s.name) =
      some {x | sourceEquiv B s x ∈
        (Pattern.bottom s).denote (sourceValuation B objects)} := by
  simp [Builtins.Semantics.denote, declared, Pattern.denote]

theorem source_integer (B : Carriers M) (objects : Builtins.Semantics.Values M)
    (text : String) (n : Int) (fuel : Nat)
    (parsed : Literal.parse SortBindings.intSort text = some (.integer n)) :
    Builtins.Semantics.denote scope [] M B (fuel + 1) [] objects SortBindings.intSort
      (.domainValue SortBindings.intSort text) = some {x | B.integer x = n} := by
  have singleton : ({B.integer.symm n} : Set (M.carrier SortBindings.intSort)) =
      {x | B.integer x = n} := by
    ext x
    constructor
    · intro h
      change x = B.integer.symm n at h
      simp [h]
    · intro h
      change x = B.integer.symm n
      change B.integer x = n at h
      apply B.integer.injective
      simpa only [Equiv.apply_symm_apply] using h
  simpa [Builtins.Semantics.denote, parsed, Literal.sort, Carriers.literal] using
    congrArg some singleton

theorem source_boolean (B : Carriers M) (objects : Builtins.Semantics.Values M)
    (text : String) (b : Bool) (fuel : Nat)
    (parsed : Literal.parse SortBindings.boolSort text = some (.boolean b)) :
    Builtins.Semantics.denote scope [] M B (fuel + 1) [] objects SortBindings.boolSort
      (.domainValue SortBindings.boolSort text) = some {x | B.boolean x = b} := by
  have singleton : ({B.boolean.symm b} : Set (M.carrier SortBindings.boolSort)) =
      {x | B.boolean x = b} := by
    ext x
    constructor
    · intro h
      change x = B.boolean.symm b at h
      simp [h]
    · intro h
      change x = B.boolean.symm b
      change B.boolean x = b at h
      apply B.boolean.injective
      simpa only [Equiv.apply_symm_apply] using h
  simpa [Builtins.Semantics.denote, parsed, Literal.sort, Carriers.literal] using
    congrArg some singleton

/-- Complement is preimage complement; it is not the BOOL.not hook. -/
theorem source_neg (B : Carriers M) (objects : Builtins.Semantics.Values M)
    (s : ValueSort) (fuel : Nat) (raw : RawPattern) (p : Pattern s)
    (child : Builtins.Semantics.denote scope [] M B fuel [] objects s.name raw =
      some {x | sourceEquiv B s x ∈ p.denote (sourceValuation B objects)}) :
    Builtins.Semantics.denote scope [] M B (fuel + 1) [] objects s.name (.neg s.name raw) =
      some {x | sourceEquiv B s x ∈
        (Pattern.neg p).denote (sourceValuation B objects)} := by
  simp [Builtins.Semantics.denote, child, Pattern.denote]
  ext x
  rfl

theorem source_conj (B : Carriers M) (objects : Builtins.Semantics.Values M)
    (s : ValueSort) (fuel : Nat) (raw other : RawPattern) (p q : Pattern s)
    (left : Builtins.Semantics.denote scope [] M B fuel [] objects s.name raw =
      some {x | sourceEquiv B s x ∈ p.denote (sourceValuation B objects)})
    (right : Builtins.Semantics.denote scope [] M B fuel [] objects s.name other =
      some {x | sourceEquiv B s x ∈ q.denote (sourceValuation B objects)}) :
    Builtins.Semantics.denote scope [] M B (fuel + 1) [] objects s.name (.conj s.name raw other) =
      some {x | sourceEquiv B s x ∈
        (Pattern.conj p q).denote (sourceValuation B objects)} := by
  simp [Builtins.Semantics.denote, left, right, Pattern.denote]
  ext x
  rfl

theorem source_disj (B : Carriers M) (objects : Builtins.Semantics.Values M)
    (s : ValueSort) (fuel : Nat) (raw other : RawPattern) (p q : Pattern s)
    (left : Builtins.Semantics.denote scope [] M B fuel [] objects s.name raw =
      some {x | sourceEquiv B s x ∈ p.denote (sourceValuation B objects)})
    (right : Builtins.Semantics.denote scope [] M B fuel [] objects s.name other =
      some {x | sourceEquiv B s x ∈ q.denote (sourceValuation B objects)}) :
    Builtins.Semantics.denote scope [] M B (fuel + 1) [] objects s.name (.disj s.name raw other) =
      some {x | sourceEquiv B s x ∈
        (Pattern.disj p q).denote (sourceValuation B objects)} := by
  simp [Builtins.Semantics.denote, left, right, Pattern.denote]
  ext x
  rfl

end Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt
