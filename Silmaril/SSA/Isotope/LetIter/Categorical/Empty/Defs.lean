module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Thms
public import Silmaril.SSA.Isotope.Bridge.Defs
public import Silmaril.Raw.SSA.Isotope.Institution.InstrSig

/-! # Closed reification and semantic reflection in the syntactic model -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open Silmaril.Thesis.LambdaIter.Syn.SynCat

universe u v

/-- Denotation in the canonical strong Elgot Freyd model of the native signature. -/
noncomputable def denoteInSyntax {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
    {ν : Type v} [DecidableEq ν] (pe : ε) {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : LocallyNameless.Tm ν Φ n} {A : τ} (d : LocallyNameless.Derivation Φ Γ β t A) :
    (values (signature (τ := τ) (Φ := Φ) pe)).obj (envObj (typeModel (Φ := Φ) pe) Γ β) ⟶
      (values (signature (τ := τ) (Φ := Φ) pe)).obj (valueObj (Φ := Φ) pe A) :=
  letI := instructionModel (τ := τ) (Φ := Φ) pe
  denote (values (signature (τ := τ) (Φ := Φ) pe)) (typeModel pe) d

/-- The closed instance of native denotation reification into the existing exact quotient. -/
def ClosedReification : Prop :=
  ∀ {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε),
    letI := Bridge.thesisTypeFormers τ
    letI := Bridge.thesisHasTy Φ τ
    ∀ {t : LocallyNameless.Tm Empty Φ 0} {A : τ}
      (d : LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) .nil t A)
      (h : Silmaril.Thesis.LambdaIter.LocallyNameless.HasType (signature (τ := τ) (Φ := Φ) pe).Instr
        .nil .nil (Bridge.toThesis t) A),
      (values (signature (τ := τ) (Φ := Φ) pe)).map (packedEnvIso (Φ := Φ) pe .nil).inv ≫
        denoteInSyntax pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h

/-- The closed instance of reflection from the syntactic model back into the exact theory. -/
def ClosedReflection : Prop :=
  ∀ {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] (pe : ε)
    {t s : LocallyNameless.Tm Empty Φ 0} {A : τ}
    (d : LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) .nil t A)
    (e : LocallyNameless.Derivation Φ (Ctx.nil : Ctx Empty τ) .nil s A),
    denoteInSyntax pe d = denoteInSyntax pe e → LocallyNameless.Equiv pe .nil .nil t s A

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.AbortCounterexample

/-- Two effectful primitives with a unit input and an empty result. -/
def signature : Institution.InstrSig (Ty Empty) Bool where
  Instr := Bool
  hasTy := ⟨fun _ => .unit, fun _ => .empty⟩
  hasEff := ⟨fun _ => true⟩

end Silmaril.Isotope.LetIter.Semantics.Categorical.AbortCounterexample
