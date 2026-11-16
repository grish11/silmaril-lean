module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Checking

/-! Explicit transport for the raw-source adequacy obligation. These definitions
retain arbitrary source carriers and finite raw environments; they do not assume
that a successful syntactic check makes a missing variable binding legal. -/
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
variable [SortBindings]

/-- The existing source builtin equivalences, without identifying carrier types. -/
def sourceEquiv {scope : Modules.Scope}
    {M : Matching.GeneralFixedPoint.Model scope.signature} (B : Carriers M) :
    (s : ValueSort) → M.carrier s.name ≃ s.Value
  | .integer => B.integer
  | .boolean => B.boolean

/-- Missing bindings remain distinguishable in LegalObjects below. This total
valuation is only used for the supported, actually bound source variables. -/
def sourceValuation {scope : Modules.Scope}
    {M : Matching.GeneralFixedPoint.Model scope.signature} (B : Carriers M)
    (objects : Semantics.Values M) : Valuation := fun s name =>
  {x | (sourceEquiv B s).symm x ∈
    (Semantics.lookupValue M objects name s.name).getD ∅}

def Pattern.variables : {s : ValueSort} → Pattern s → List (ValueSort × String)
  | _, .variable s name => [(s, name)]
  | _, .integer _ | _, .boolean _ | _, .top _ | _, .bottom _ => []
  | _, .neg p => p.variables
  | _, .boolNot p => p.variables
  | _, .conj p q => p.variables ++ q.variables
  | _, .disj p q => p.variables ++ q.variables
  | _, .intEq p q => p.variables ++ q.variables

/-- Each referenced raw object binding exists at its exact sort. Values can be
empty or nonsingleton sets; no singleton or global total-name assumption. -/
def LegalObjects {scope : Modules.Scope}
    {M : Matching.GeneralFixedPoint.Model scope.signature}
    (objects : Semantics.Values M) {s : ValueSort} (p : Pattern s) : Prop :=
  ∀ binding ∈ p.variables,
    (Semantics.lookupValue M objects binding.2 binding.1.name).isSome = true

/-- Exact original-source adequacy proposition. The public rawAdequacy theorem
in Thms proves this statement via the independent raw interpreter. -/
def Task.rawAdequacy : Prop :=
  ∀ (scope : Modules.Scope) (hooks : List HookBinding)
    (literalPrefix : String) (literals : List LiteralBinding)
    (M : Model scope literalPrefix literals hooks)
    (objects : Semantics.Values M.native) (fuel : Nat) (s : ValueSort)
    (raw : RawPattern) (p : Pattern s),
    check scope hooks fuel s raw = some p → LegalObjects objects p →
    Semantics.denote scope [] M.native M.carriers fuel [] objects s.name raw =
      some {x | sourceEquiv M.carriers s x ∈ p.denote (sourceValuation M.carriers objects)}

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
