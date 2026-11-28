module

public import Silmaril.SSA.Isotope.LetParCase.Thms
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

/-- Widening the case tier to the iteration tier is injective on syntax. -/
theorem ofLetParCase_injective {ν : Type w} {Φ : Type q} {n : Nat} :
    Function.Injective (ofLetParCase : LetParCase.Tm ν Φ n → Tm ν Φ n) :=
  Parallel.Tm.widen_injective Parallel.Tier.caseIter

/-- Both successive widenings preserve equality of sequential-tier syntax. -/
theorem ofLetPar_injective {ν : Type w} {Φ : Type q} {n : Nat} :
    Function.Injective (ofLetPar : LetPar.Tm ν Φ n → Tm ν Φ n) :=
  ofLetParCase_injective.comp LetParCase.ofLetPar_injective

/-- The native case inclusion and the parallel case inclusion commute. -/
theorem embed_caseIter {ν : Type w} {Φ : Type q} {n : Nat}
    (t : LetCase.LocallyNameless.Tm ν Φ n) :
    embed (Morphism.CaseIter.embed t) = ofLetParCase (LetParCase.embed t) :=
  Proofs.embed_caseIter t

/-- The sequential-to-iteration rectangle is the composite of the two squares. -/
theorem embed_seqIter {ν : Type w} {Φ : Type q} {n : Nat}
    (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    embed (Morphism.CaseIter.embed (Morphism.SeqCase.embed t)) =
      ofLetPar (LetPar.embed t) := by
  rw [embed_caseIter, LetParCase.embed_seqCase]
  rfl

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

/-- Moving a native term under a binder commutes with embedding. -/
@[simp] theorem embed_underBinder {ν : Type w} {Φ : Type q} {n : Nat}
    (t : LetIter.LocallyNameless.Tm ν Φ (n + 1)) :
    embed t.underBinder = (embed t).underBinder :=
  embed_rename _ _

/-- Opening a native binder commutes with embedding. -/
@[simp] theorem embed_instantiate {ν : Type w} {Φ : Type q} {n : Nat}
    (b : LetIter.LocallyNameless.Tm ν Φ (n + 1)) (a : LetIter.LocallyNameless.Tm ν Φ n) :
    embed (b.instantiate a) = (embed b).instantiate (embed a) := by
  rw [LetIter.LocallyNameless.Tm.instantiate, embed_bsubst, Parallel.Tm.instantiate]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- The native purity guard is preserved by the embedding. -/
theorem embed_pure {ν : Type w} {Φ : Type q} {ε : Type r} [HasEff Φ ε] {pe : ε} {n : Nat}
    {t : LetIter.LocallyNameless.Tm ν Φ n}
    (h : LetIter.LocallyNameless.Pure pe t) : Parallel.Pure pe (embed t) :=
  Proofs.embed_pure h

section NativeEquations

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]
  {pe : ε} {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- Native proof-relevant equations at exact endpoints, including recursive
uniformity, hold at their embedded typing derivations. -/
theorem embed_related {a b : LetIter.LocallyNameless.Tm ν Φ n}
    (da : LetIter.LocallyNameless.Derivation Φ Γ β a A)
    (db : LetIter.LocallyNameless.Derivation Φ Γ β b A)
    (eq : LetIter.ProofRelevant.LocallyNameless.TypedEquiv.Related pe Γ
      (nativeTyping da) (nativeTyping db)) :
    Equiv pe Γ (derivation da) (derivation db) :=
  .native da db eq

end NativeEquations

section Widen

open Isotope.Semantics

variable {τ : Type u} [TypeFormers τ] (D : τ → Type v)
  [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  {m : Type v → Type v} [Monad m] [Elgot.Iterate m]
  (M : InstructionModel D Φ m) (P : ParOp m)
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- The common denotation commutes with widening from the case tier. -/
theorem denote_ofLetParCaseDerivation {a : LetParCase.Tm ν Φ n}
    (d : Derivation Φ Γ β a A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (ofLetParCaseDerivation d).denote D M P (iterControl D m) γ ρ =
      d.denote D M P (Control.case D m) γ ρ :=
  Proofs.denote_ofLetParCaseDerivation D M P d γ ρ

/-- The common denotation commutes with the composite sequential-tier inclusion. -/
theorem denote_ofLetParDerivation {a : LetPar.Tm ν Φ n}
    (d : Derivation Φ Γ β a A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (ofLetParDerivation d).denote D M P (iterControl D m) γ ρ =
      d.denote D M P (Control.seq D m) γ ρ :=
  (denote_ofLetParCaseDerivation D M P (LetParCase.ofLetParDerivation d) γ ρ).trans
    (LetParCase.denote_ofLetParDerivation D M P d γ ρ)

end Widen

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

include P in
/-- Equality of embedded endpoints implies equality in every native model
equipped with a lawful parallel pairing. -/
theorem native_denote_eq {a b : LetIter.LocallyNameless.Tm ν Φ n}
    {da : LetIter.LocallyNameless.Derivation Φ Γ β a A}
    {db : LetIter.LocallyNameless.Derivation Φ Γ β b A}
    (h : Equiv (⊥ : ε) Γ (derivation da) (derivation db)) (γ : CtxDen Γ) (ρ : BoundDen β) :
    LetIter.ProofRelevant.Semantics.denote (ε := ε) (m := m) (nativeTyping da) γ ρ =
      LetIter.ProofRelevant.Semantics.denote (ε := ε) (m := m) (nativeTyping db) γ ρ :=
  (denote_embed P da γ ρ).symm.trans ((sound P h γ ρ).trans (denote_embed P db γ ρ))

end Silmaril.Isotope.LetParIter
