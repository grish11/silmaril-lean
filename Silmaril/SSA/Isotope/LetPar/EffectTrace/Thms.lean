module

public import Silmaril.SSA.Isotope.LetPar.EffectTrace.Defs
public import Silmaril.SSA.Isotope.LetPar.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetPar.EffectTrace

/-! # Trace separation and concrete conservativity for LetSeq in LetPar -/

public section

namespace Silmaril.Isotope.LetPar.EffectTrace

universe u v w r

variable {ν : Type w} {Φ : Type v} {ε : Type r} [HasEff Φ ε] [DecidableEq ε]
  {pureEff : ε} {n : Nat}

/-- An effectful instruction word is observed in its original order. -/
theorem observe_word (fs : List Φ) (effectful : ∀ f ∈ fs, (instrEff f : ε) ≠ pureEff) :
    observe pureEff (LetPar.embed (word (ν := ν) (n := n) fs)) = some fs :=
  Proofs.observe_word fs effectful

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

/-- Every derivable LetPar equation preserves the trace, including proofs that pass through
parallel terms. -/
theorem observe_equiv {a b : Tm ν Φ n} (h : LetPar.Equiv pureEff Γ β a b A) :
    observe pureEff a = observe pureEff b :=
  Proofs.observe_equiv h

/-- A word is typable whenever its opcodes accept unit arguments. -/
theorem word_hasType (fs : List Φ) (source : ∀ f ∈ fs, instrSrc f = (Silmaril.unit : τ)) :
    LetSeq.LocallyNameless.HasType Φ Γ β (word fs) Silmaril.unit :=
  Proofs.word_hasType fs source

/-- The full LetPar theory separates distinct effectful instruction words. -/
theorem word_eq_of_equiv {fs gs : List Φ}
    (effectfulF : ∀ f ∈ fs, (instrEff f : ε) ≠ pureEff)
    (effectfulG : ∀ g ∈ gs, (instrEff g : ε) ≠ pureEff)
    (h : LetPar.Equiv pureEff Γ β (LetPar.embed (word fs)) (LetPar.embed (word gs)) Silmaril.unit) :
    fs = gs :=
  Proofs.word_eq_of_equiv effectfulF effectfulG h

/-- The inclusion reflects equations on effectful words fed a unit argument. -/
theorem word_equiv_iff {fs gs : List Φ}
    (source : ∀ f ∈ fs, instrSrc f = (Silmaril.unit : τ))
    (effectfulF : ∀ f ∈ fs, (instrEff f : ε) ≠ pureEff)
    (effectfulG : ∀ g ∈ gs, (instrEff g : ε) ≠ pureEff) :
    LetPar.Equiv pureEff Γ β (LetPar.embed (word fs)) (LetPar.embed (word gs)) Silmaril.unit ↔
      LetSeq.LocallyNameless.Equiv pureEff Γ β (word fs) (word gs) Silmaril.unit :=
  Proofs.word_equiv_iff source effectfulF effectfulG

end Silmaril.Isotope.LetPar.EffectTrace

namespace Silmaril.Isotope.LetPar.EffectTrace.Singleton

universe v r

variable {Φ : Type v} {ε : Type r} [HasEff Φ ε] [DecidableEq ε] {pureEff : ε}
  {n : Nat} {β : BoundCtx Unit n}

/-- Ordered traces characterize native equivalence over the single object type. -/
theorem observe_eq_iff {a b : LetSeq.LocallyNameless.Tm Empty Φ n} :
    observe pureEff (LetPar.embed a) = observe pureEff (LetPar.embed b) ↔
      LetSeq.LocallyNameless.Equiv pureEff (Ctx.nil : Ctx Empty Unit) β a b Silmaril.unit :=
  Proofs.observe_eq_iff

/-- With one object type and an empty free context, every source term has an effect word.
At every bound context the LetSeq inclusion reflects its equational theory. -/
theorem equiv_iff {a b : LetSeq.LocallyNameless.Tm Empty Φ n} :
    LetPar.Equiv pureEff (Ctx.nil : Ctx Empty Unit) β (LetPar.embed a) (LetPar.embed b) Silmaril.unit ↔
      LetSeq.LocallyNameless.Equiv pureEff (Ctx.nil : Ctx Empty Unit) β a b Silmaril.unit :=
  ⟨fun eq => observe_eq_iff.mp (observe_equiv eq), LetPar.embed_equiv⟩

end Silmaril.Isotope.LetPar.EffectTrace.Singleton
