module

public import Silmaril.Semantics.Calco2019.Examples.Printing.TraceIteration.Defs
public import Silmaril.Semantics.Calco2019.Examples.TypeKleisli.Thms
import Silmaril.Proofs.Semantics.Calco2019.Examples.TraceGuardedElgot

/-! # The guarded Elgot monad for finite and productive infinite traces -/

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing

variable {A X Y Z : Type u}

/-- The nonempty-word guard satisfies Definition 6. -/
def productiveGuard (A : Type u) : TypeKleisli.Guard (NonemptyTrace A) :=
  ProductiveProofs.guard A

theorem productiveGuard_iff (f : X → NonemptyTrace A (Y ⊕ Z)) :
    (productiveGuard A).holds f ↔ ProductiveGuard f := by
  unfold productiveGuard
  rfl

/-- The greatest trace solution satisfies the fixpoint, naturality, codiagonal,
and pure uniformity equations. -/
noncomputable def productiveLaws (A : Type u) :
    TypeKleisli.Iteration (NonemptyTrace A) (productiveGuard A) :=
  ProductiveProofs.laws A

theorem productiveLaws_run (f : X → NonemptyTrace A (Y ⊕ X)) (hf : (productiveGuard A).holds f) :
    (productiveLaws A).run f hf = productiveIter f ((productiveGuard_iff f).mp hf) :=
  ProductiveProofs.laws_run f hf

/-- Examples 10(5) and 20(5), including all guarded Conway laws. -/
noncomputable def productiveElgot (A : Type u) : GuardedElgotMonad typeCoproducts.{u} :=
  TypeKleisli.assemble (productiveLaws A)

/-- The chosen solution for the separating equation exceeds the finite-only fixpoint. -/
theorem canonical_not_least (a : A) : ¬ greatestTrace (traceLoop a) ≤ finiteSolution a :=
  ProductiveProofs.canonical_not_least a

/-- A nonempty alphabet admits the separating guarded loop with two fixpoints. -/
theorem productive_not_iterative {A : Type} (a : A) :
    ¬ (TypeKleisli.categoricalGuard (productiveGuard A)).Iterative := by
  rw [TypeKleisli.iterative_iff]
  exact ProductiveProofs.productive_not_unique A a

end Silmaril.Calco2019.Examples.Printing
