module

public import Silmaril.SSA.Isotope.LetParIter.Equations.Defs
public import Silmaril.SSA.Isotope.LetParIter.Shared.Defs
public import Silmaril.SSA.Isotope.LetParIter.Semantics.Thms
public import Silmaril.Semantics.Elgot.Parallel.Thms
import Silmaril.Proofs.SSA.Isotope.LetParIter.Native
import Silmaril.Proofs.SSA.Isotope.LetParIter.Soundness
import Silmaril.Proofs.SSA.Isotope.LetParIter.Shared

/-! # Native syntax inclusion and generic soundness for LetParIter -/

public section

namespace Silmaril.Isotope.LetParIter

open Parallel LetIter.ProofRelevant.Semantics

universe u v w q r

/-- The recognizer is a left inverse on native syntax. -/
@[simp] theorem toLetIter?_embed {ν : Type w} {Φ : Type q} {n : Nat}
    (t : LetIter.LocallyNameless.Tm ν Φ n) : toLetIter? (embed t) = some t :=
  Proofs.toLetIter?_embed t

/-- Including parallel-free syntax is injective. -/
theorem embed_injective {ν : Type w} {Φ : Type q} {n : Nat} :
    Function.Injective (embed : LetIter.LocallyNameless.Tm ν Φ n → Tm ν Φ n) :=
  fun _ _ h => Option.some.inj (by simpa only [toLetIter?_embed] using congrArg toLetIter? h)

/-- The native case inclusion and the parallel case inclusion commute. -/
theorem embed_caseIter {ν : Type w} {Φ : Type q} {n : Nat}
    (t : LetCase.LocallyNameless.Tm ν Φ n) :
    embed (Morphism.CaseIter.embed t) = ofLetParCase (LetParCase.embed t) :=
  Proofs.embed_caseIter t

/-- The embedding commutes with bound renaming, including under iteration. -/
@[simp] theorem embed_rename {ν : Type w} {Φ : Type q} {n k : Nat}
    (r : Fin n → Fin k) (t : LetIter.LocallyNameless.Tm ν Φ n) :
    embed (t.rename r) = (embed t).rename r :=
  Proofs.embed_rename r t

/-- The embedding commutes with simultaneous capture-avoiding bound substitution. -/
@[simp] theorem embed_bsubst {ν : Type w} {Φ : Type q} {n k : Nat}
    (σ : Fin n → LetIter.LocallyNameless.Tm ν Φ k) (t : LetIter.LocallyNameless.Tm ν Φ n) :
    embed (t.bsubst σ) = (embed t).bsubst (fun i => embed (σ i)) :=
  Proofs.embed_bsubst σ t

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [Elgot.Iterate m] [InstructionModel Φ τ ε m]
variable (P : Elgot.ParallelPairing m)
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- Native terms keep their monadic denotation for every interpretation of parallel. -/
theorem denote_embed {t : LetIter.LocallyNameless.Tm ν Φ n}
    (d : LetIter.LocallyNameless.Derivation Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (ε := ε) P (derivation d) γ ρ =
      LetIter.ProofRelevant.Semantics.denote (ε := ε) (nativeTyping d) γ ρ :=
  Proofs.denote_embed P d γ ρ

variable [LawfulMonad m]

/-- The common tier interpreter agrees with the direct native-model denotation. -/
theorem interpret_eq_denote {a : Tm ν Φ n} (d : Derivation Φ Γ β a A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    interpret (ε := ε) P d γ ρ = denote (ε := ε) P d γ ρ :=
  Proofs.interpret_eq_denote P d γ ρ

variable [Elgot.LawfulElgotMonad m]

/-- Every equation preserves denotation at its specified typing derivations.
The Elgot laws account for feedback, and the parallel pairing accounts for
parallel tuple coherence and pure maps. -/
theorem sound {a b : Tm ν Φ n} {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A}
    (h : Equiv (⊥ : ε) Γ da db) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (ε := ε) P da γ ρ = denote (ε := ε) P db γ ρ :=
  Proofs.sound P γ ρ h

/-- Generated equations preserve the common tier interpreter under the same laws. -/
theorem interpret_sound {a b : Tm ν Φ n} {da : Derivation Φ Γ β a A}
    {db : Derivation Φ Γ β b A} (h : Equiv (⊥ : ε) Γ da db) (γ : CtxDen Γ) (ρ : BoundDen β) :
    interpret (ε := ε) P da γ ρ = interpret (ε := ε) P db γ ρ := by
  simpa only [interpret_eq_denote] using sound P h γ ρ

end Silmaril.Isotope.LetParIter
