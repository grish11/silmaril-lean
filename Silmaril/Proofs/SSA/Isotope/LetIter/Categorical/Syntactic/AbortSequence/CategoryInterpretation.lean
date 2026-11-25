module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Interpretation.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.AbortSequence.Thms

/-! # Interpretation of repaired computation arrows -/

public section

universe u u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.InterpretationProofs

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation)
open Silmaril.Thesis.LambdaIter.Syn (Carrier SynCat mk)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ

private theorem nativeTyping {X Y : SynCat modelSig} (a : Carrier modelSig (.snoc .nil X.ty) Y.ty) :
    Nonempty (Derivation Φ Γ₀ (.snoc .nil X.ty) (Bridge.ofThesis a.1) Y.ty) := by
  apply Derivation.ofHasType
  apply (Bridge.hasType_iff (Bridge.TypeCompat.canonical τ) (Bridge.InstrCompat.canonical Φ τ)).mpr
  simpa only [Bridge.Ctx.toThesis, Bridge.BoundCtx.toThesis, Bridge.toThesis_ofThesis] using a.2

variable
  (coherent : TypingCoherent (ν := Empty) J M Φ)
  (shared : ∀ R T : V, ∃ e : J.obj R ⊗ J.obj T = J.obj (R ⊗ T),
    Functor.StrongPremonoidal.tensorIso (J := J) R T = eqToIso e)
  (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
    InstructionModel.denote (J := J) (M := M) f = J.map p)

private noncomputable def denoteClass {X Y : SynCat modelSig} :
    Quotient (repairedHomSetoid pe X Y) → (J.obj (M.obj X.ty) ⟶ J.obj (M.obj Y.ty)) :=
  Quotient.lift
    (fun a => J.map (singletonEnvIso M X.ty).inv ≫ denote J M (nativeTyping pe a).some)
    (fun _ _ h => congrArg (J.map (singletonEnvIso M X.ty).inv ≫ ·)
      (denote_abortEquiv_of_coherent_shared_tensor J M coherent shared pureInstr h _ _))

noncomputable def repairedArrowDenote {X Y : Q} (f : X ⟶ Y) :
    J.obj (M.obj X.as.ty) ⟶ J.obj (M.obj Y.as.ty) :=
  Quot.liftOn f (fun g => denoteClass pe J M coherent shared pureInstr (repairedHomClass pe g))
    (fun g h e => congrArg (denoteClass pe J M coherent shared pureInstr)
      ((HomRel.compClosure_iff_self (repairedHomRel pe) g h).mp e))

theorem repairedArrowDenote_mk {X Y : SynCat modelSig}
    {t : Thesis.LambdaIter.LocallyNameless.Tm Empty Φ 1}
    (h : Thesis.LambdaIter.LocallyNameless.HasType Φ .nil (.snoc .nil X.ty) t Y.ty)
    (d : Derivation Φ Γ₀ (.snoc .nil X.ty) (Bridge.ofThesis t) Y.ty) :
    repairedArrowDenote pe J M coherent shared pureInstr
        ((P).map (mk (S := modelSig) h : X ⟶ Y)) =
      J.map (singletonEnvIso M X.ty).inv ≫ denote J M d := by
  change J.map (singletonEnvIso M X.ty).inv ≫ denote J M _ = _
  rw [coherent _ d]

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.InterpretationProofs
