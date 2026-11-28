module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Model.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Model

/-! # Reflect native outward-region denotations into exact LetCase equations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Semantics.Categorical (denoteRegion RegionTypingCoherent denoteSingletonRegion labelInject)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LetCase.Structural.Finite (Types Context StructuralContext)
open scoped MonoidalCategory LetCase.Structural.Finite LetSeq.StraightLine.Structural

section Model

universe u v u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
/-- The existing typed LetCase inclusion preserves its categorical arrow. -/
theorem denote_caseIter {n : Nat} {β : BoundCtx τ n} {t : LetCase.LocallyNameless.Tm Empty Φ n} {A : τ}
    (d : LetCase.LocallyNameless.Derivation Φ (.nil : Ctx Empty τ) β t A) :
    LetIter.Semantics.Categorical.denote J M (Morphism.CaseIter.derivation d) =
      LetCase.Semantics.Categorical.denote J M d :=
  denote_caseIter_proof J M d

/-- An exact realization of the written region computes its native categorical
arrow, independently of the selected typing and code witnesses. -/
theorem Endpoint.denote_code {n : Nat} {β : BoundCtx τ n} {A : τ} (p : Endpoint Φ β A)
    (c : Code Φ β A) (written : c.toSSA 0 = p.region) :
    denoteRegion J M p.typed = J.map (contextMap M β) ≫
      LetCase.Semantics.Categorical.denote J M c.toLetCase.2 ≫
      J.map (labelInject M 0 (rfl : At [A] 0 A)) :=
  denote_code_proof J M p c written

/-- Equality at the original typed endpoints is exactly equality after
compilation in the same model. The context and singleton exit maps cancel. -/
theorem Endpoint.denote_eq_iff {n : Nat} {β : BoundCtx τ n} {A : τ} (p q : Endpoint Φ β A) :
    denoteRegion J M p.typed = denoteRegion J M q.typed ↔
      LetCase.Semantics.Categorical.denote J M p.compile.2 =
        LetCase.Semantics.Categorical.denote J M q.compile.2 :=
  denote_eq_iff_proof J M p q

/-- The comparison also uses the actual singleton arrows when the source is
one packed input. -/
theorem Endpoint.denoteSingleton_eq_iff {X A : τ} (p q : Endpoint Φ (.snoc .nil X) A) :
    denoteSingletonRegion J M p.typed = denoteSingletonRegion J M q.typed ↔
      LetCase.Semantics.Categorical.denote J M p.compile.2 =
        LetCase.Semantics.Categorical.denote J M q.compile.2 :=
  denoteSingleton_eq_iff_proof J M p q

end Model

/-- A LetCase equation at any exact code witnesses proves validity of the
original written regions. The chosen compile witnesses are unnecessary here. -/
theorem Endpoint.valid_of_code_equiv {Φ : Type} [LetCase.Structural.Finite.Signature Φ]
    {n : Nat} {β : Context n} {A : Types} (p q : Endpoint Φ β A) (c d : Code Φ β A)
    (hc : c.toSSA 0 = p.region) (hd : d.toSSA 0 = q.region)
    (eq : LetCase.LocallyNameless.Equiv false LetCase.Structural.Reply.Γ₀ β
      c.toLetCase.1 d.toLetCase.1 A) : p.Valid q :=
  valid_of_code_equiv_proof p q c d hc hd eq

open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)

/-- The free structural ordered-trace interpretation has coherent native
region witnesses at every exact input and exit interface. -/
theorem trace_region_coherent {Φ : Type} [HasTy Φ Types] :
    letI := traceInstructions (α := Empty) (Φ := Φ)
    RegionTypingCoherent (Φ := Φ) (traceJ (α := Empty) (Φ := Φ)) (traceTypes Empty) :=
  trace_region_coherent_proof

/-- For independently admitted outward regions, categorical validity at the
original exact arrows is equivalent to native derivability after LetCase
compilation. The chosen ordered trace model satisfies both coherences. -/
theorem Endpoint.valid_iff_compiled {Φ : Type} [LetCase.Structural.Finite.Signature Φ]
    {n : Nat} {β : Context n} {A : Types} (input : StructuralContext β) (p q : Endpoint Φ β A) :
    p.Valid q ↔ LetCase.LocallyNameless.Equiv false LetCase.Structural.Reply.Γ₀ β p.compile.1 q.compile.1 A :=
  valid_iff_compiled_proof input p q

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
