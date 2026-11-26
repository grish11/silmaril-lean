module

public import Silmaril.SSA.Isotope.LetParIter.Equations.Defs
public import Silmaril.SSA.Isotope.LetParIter.Interpretation.Defs
public import Silmaril.SSA.Isotope.LetParIter.Semantics.Thms
public import Silmaril.Semantics.Elgot.Parallel.Thms
import Silmaril.Proofs.SSA.Isotope.LetParIter.Native
import Silmaril.Proofs.SSA.Isotope.LetParIter.Soundness

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

variable [LawfulMonad m] [Elgot.LawfulElgotMonad m]

/-- Every equation preserves denotation at its specified typing derivations.
The Elgot laws account for feedback, and the parallel pairing accounts for
parallel tuple coherence and pure maps. -/
theorem sound {a b : Tm ν Φ n} {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A}
    (h : Equiv (⊥ : ε) Γ da db) (γ : CtxDen Γ) (ρ : BoundDen β) :
    denote (ε := ε) P da γ ρ = denote (ε := ε) P db γ ρ :=
  Proofs.sound P γ ρ h

end Silmaril.Isotope.LetParIter
