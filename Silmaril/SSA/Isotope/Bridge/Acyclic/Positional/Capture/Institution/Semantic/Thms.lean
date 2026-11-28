module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Semantic.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Semantic.Inverses

/-! # The captured institutions agree on semantic sentence classes

The quotient compares satisfaction in the chosen models. It gives no
completeness result for a syntactic rewrite theory.
-/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Inst CoIns)
open Silmaril.SSA.LambdaRTL.Quotient (semSetoid quotFunctor)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

theorem ranked_roundTrip_semantic (e : RankedEquation P) :
    (semSetoid (rankedRoom J P)).r (numberGrammar (readGrammar e)) e :=
  fun K => ranked_roundTrip_proof K e

omit [FreydCategory.CentralUnit J] in
theorem grammar_roundTrip_semantic (e : GrammarEquation P) :
    (semSetoid (grammarRoom J P)).r (readGrammar (numberGrammar e)) e :=
  fun A => grammar_roundTrip_proof A e

theorem read_number_quot (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) :
    quotFunctor.map (readCorridor J P) ≫ quotFunctor.map (numberCorridor J P) =
      𝟙 (quotFunctor.obj (rankedRoom J P)) :=
  read_number_quot_proof J P

theorem number_read_quot (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) :
    quotFunctor.map (numberCorridor J P) ≫ quotFunctor.map (readCorridor J P) =
      𝟙 (quotFunctor.obj (grammarRoom J P)) :=
  number_read_quot_proof J P

/-- The forward square is exact on typed grammar witnesses. Its inverse
on satisfaction classes is natural over all type-former-preserving maps. -/
noncomputable def semanticNaturalIso (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] :
    (rankedSemanticInstitution J).I ≅ (grammarSemanticInstitution J).I :=
  NatIso.ofComponents (fun (P : TypeSignature) => ⟨quotFunctor.map (readCorridor J P.prim),
    quotFunctor.map (numberCorridor J P.prim), read_number_quot J P.prim,
    number_read_quot J P.prim⟩)
    (fun f => (Functor.whiskerRight (readNatural J) quotFunctor).naturality f)

noncomputable def semanticCompile (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] :
    Inst.CoHom (rankedSemanticInstitution J) (grammarSemanticInstitution J) where
  Φ := 𝟭 TypeSignature
  ρ := (semanticNaturalIso J).hom ≫ (Functor.leftUnitor _).inv

noncomputable def semanticReify (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] :
    Inst.CoHom (grammarSemanticInstitution J) (rankedSemanticInstitution J) where
  Φ := 𝟭 TypeSignature
  ρ := (semanticNaturalIso J).inv ≫ (Functor.leftUnitor _).inv

/-- The inverse comorphisms use the same signatures and the existing
validated/coherent model isomorphism. -/
noncomputable def semanticInstitutionIso (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] :
    Iso (C := CoIns.{1, 0, 0, 0, 1}) (rankedSemanticInstitution J) (grammarSemanticInstitution J) where
  hom := semanticCompile J
  inv := semanticReify J
  hom_inv_id := Inst.CoHom.ext rfl (NatTrans.ext (funext fun (P : TypeSignature) => read_number_quot J P.prim))
  inv_hom_id := Inst.CoHom.ext rfl (NatTrans.ext (funext fun (P : TypeSignature) => number_read_quot J P.prim))

end Silmaril.Isotope.Institution.Acyclic.Captured
