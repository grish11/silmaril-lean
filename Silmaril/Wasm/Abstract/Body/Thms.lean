module

public import Silmaril.Wasm.Abstract.Body.Defs
public import Silmaril.Semantics.IterOps.Thms
import Silmaril.Proofs.Wasm.Abstract.Body.Basic

/-!
# Abstract Wasm function bodies: theorems

* `bodyM_lawfulElgot`, `bodyC_lawfulElgot`: the body monad and its coarse
  (trap ≈ divergence) quotient are lawful Elgot monads in the sense of
  `Silmaril.Elgot.LawfulElgotMonad`: fixpoint, naturality, codiagonal and
  uniformity. They are assembled from the library's proved layers, ITree,
  `ExceptT` and `StateT`.
* `thesisLawful` and the instances below: the same laws in λiter's class
  `Silmaril.Thesis.Elgot.LawfulElgotMonad`.
* `bodyM_lawfulModel`, `bodyM_initial`: hence the Kleisli category of
  `BodyM E S T`, the category of abstract bodies, is a lawful categorical model
  of λiter. For every λiter signature with an interpretation of its
  instructions as abstract bodies, the quotiented syntax maps uniquely into
  it (`Silmaril.Thesis.LambdaIter.Semantics.KleisliModel`). The same holds
  for `BodyC`.
* `collapse_pure`, `collapse_bind`, `collapse_trap`: collapsing traps into
  divergence is a monad morphism `BodyM → BodyC` that sends a trap to
  `diverge`.

**Not yet proved.** That `collapse` preserves iteration, which would make it an
Elgot (identity-on-objects) functor between the two categories. The concrete
half of the target: typed concrete Wasm bodies, their syntactic constructors,
preservation, congruence, faithfulness on the chosen quotient, image closure,
and only then the subcategory isomorphism. LetIter (`Silmaril.SSA.Isotope`)
instantiation.
-/

public section

namespace Silmaril.Wasm.Abstract.Body

open Silmaril.Games

universe u

variable {E : Sig.{u}} {S T : Type (u + 1)}

/-- The body monad is a lawful Elgot monad. -/
theorem bodyM_lawfulElgot : Silmaril.Elgot.LawfulElgotMonad (BodyM E S T) := inferInstance

/-- The coarse body monad is a lawful Elgot monad. -/
theorem bodyC_lawfulElgot : Silmaril.Elgot.LawfulElgotMonad (BodyC E S) := inferInstance

/-- The Wasm body monad is the general one at the events of the import
signature. -/
theorem bodyM_eq_gBody : BodyM E S T = GBody (SigEv E) S T := rfl

/-- The general bodies over any event family form a lawful Elgot monad. -/
theorem gBody_lawfulElgot (Ev : Type u → Type u) :
    Silmaril.Elgot.LawfulElgotMonad (GBody Ev S T) := inferInstance

/-- **Abstract Wasm bodies form a premonoidal Elgot structure**: every law of
`Silmaril.IterOps.Ops.Lawful` holds for the Kleisli operations of `BodyM`:
category, coproducts, fixpoint, naturality, codiagonal, uniformity, whiskering
and centrality of pure maps. -/
theorem bodyOps_lawful : (Silmaril.IterOps.kleisliOps (BodyM E S T)).Lawful :=
  Silmaril.IterOps.kleisli_lawful _

/-- The same for the trap ≈ divergence quotient. -/
theorem bodyCOps_lawful : (Silmaril.IterOps.kleisliOps (BodyC E S)).Lawful :=
  Silmaril.IterOps.kleisli_lawful _

/-- A lawful Elgot monad of the library satisfies λiter's lawful-Elgot class. -/
theorem thesisLawful (m : Type u → Type u) [Monad m] [LawfulMonad m] [Silmaril.Elgot.Iterate m]
    [Silmaril.Elgot.LawfulElgotMonad m] :
    @Silmaril.Thesis.Elgot.LawfulElgotMonad m _ _ (thesisIterate m) :=
  Silmaril.Proofs.Wasm.Abstract.Body.thesisLawful m

noncomputable instance : Silmaril.Thesis.Elgot.Iterate (BodyM E S T) := thesisIterate _
instance : Silmaril.Thesis.Elgot.LawfulElgotMonad (BodyM E S T) := thesisLawful _
noncomputable instance : Silmaril.Thesis.Elgot.Iterate (BodyC E S) := thesisIterate _
instance : Silmaril.Thesis.Elgot.LawfulElgotMonad (BodyC E S) := thesisLawful _

/-- Collapsing preserves `pure`. -/
theorem collapse_pure {A : Type (u + 1)} (a : A) :
    collapse (pure a : BodyM E S T A) = (pure a : BodyC E S A) :=
  Silmaril.Proofs.Wasm.Abstract.Body.collapse_pure a

/-- Collapsing preserves sequencing. -/
theorem collapse_bind {A B : Type (u + 1)} (x : BodyM E S T A) (f : A → BodyM E S T B) :
    collapse (x >>= f) = (collapse x >>= fun a => collapse (f a)) :=
  Silmaril.Proofs.Wasm.Abstract.Body.collapse_bind x f

/-- Collapsing sends a trap to divergence. -/
theorem collapse_trap {A : Type (u + 1)} (t : T) :
    collapse (trap t : BodyM E S T A) = fun _ => Silmaril.Elgot.ITree.diverge :=
  Silmaril.Proofs.Wasm.Abstract.Body.collapse_trap t

end Silmaril.Wasm.Abstract.Body

namespace Silmaril.Wasm.Abstract.Body

open _root_.CategoryTheory
open Silmaril.Thesis.LambdaIter
open Silmaril.Thesis.LambdaIter.Subtyping.Semantics
open Silmaril.Thesis.LambdaIter.Semantics
open Silmaril.Thesis.LambdaIter.LocallyNameless
open Silmaril.Thesis.Elgot

universe u w q r v

variable {E : Silmaril.Games.Sig.{u}} {St T : Type (u + 1)}
variable {τ : Type v} [TypeFormers τ] [Subtyping τ] [TypeModel.{v, u + 1} τ] [InjectiveFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable [InstructionModel Φ τ ε (BodyM E St T)]

/-- **Abstract Wasm bodies model λiter.** The Kleisli category of the body
monad is a lawful categorical model of λiter, for any interpretation of the
instructions as abstract bodies. -/
theorem bodyM_lawfulModel :
    @LocallyNameless.Categorical.LawfulModel τ _ _ ν _ Φ _ ε _ (⊥ : ε)
      (Type (u + 1)) (Kleisli (ofTypeMonad (BodyM E St T))) _ _ _ _ _ _ _ _ _ _ _ _
      (kleisliJ (BodyM E St T)) _ (Categorical.ofTypeModel (τ := τ))
      (Categorical.ofInstructionModel (ε := ε)) :=
  Silmaril.Thesis.LambdaIter.Semantics.KleisliModel.kleisli_lawfulModel

end Silmaril.Wasm.Abstract.Body
