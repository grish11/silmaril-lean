module

public import Silmaril.SSA.Isotope.LetPar.Native.Defs
public import Silmaril.SSA.Isotope.LetPar.Structural.Thms
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Equiv
public import Silmaril.Raw.SSA.Isotope.LetSeq.Semantics.Monadic
import Silmaril.Proofs.SSA.Isotope.LetPar.LetPar

@[expose] public section

namespace Silmaril.Isotope.LetPar

open Parallel Semantics

universe u v w q r

variable {ν : Type v} {Φ : Type w} {n m : Nat}

/-- The embedding reflects equality of constructor trees. -/
theorem embed_injective : Function.Injective (embed : LetSeq.LocallyNameless.Tm ν Φ n → Tm ν Φ n) :=
  Proofs.embed_injective

@[simp] theorem embed_rename (ρ : Fin n → Fin m) (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    embed (t.rename ρ) = (embed t).rename ρ :=
  Proofs.embed_rename ρ t

@[simp] theorem embed_bsubst (σ : Fin n → LetSeq.LocallyNameless.Tm ν Φ m) (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    embed (t.bsubst σ) = (embed t).bsubst (fun i => embed (σ i)) :=
  Proofs.embed_bsubst σ t

@[simp] theorem embed_instantiate (b : LetSeq.LocallyNameless.Tm ν Φ (n + 1))
    (a : LetSeq.LocallyNameless.Tm ν Φ n) :
    embed (b.instantiate a) = (embed b).instantiate (embed a) :=
  Proofs.embed_instantiate b a

theorem embed_pure {ε : Type r} [HasEff Φ ε] {pureEff : ε} {t : LetSeq.LocallyNameless.Tm ν Φ n}
    (h : LetSeq.LocallyNameless.Pure pureEff t) : Parallel.Pure pureEff (embed t) :=
  Proofs.embed_pure h

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ} {t : LetSeq.LocallyNameless.Tm ν Φ n}

theorem embed_hasType (h : LetSeq.LocallyNameless.HasType Φ Γ β t A) :
    Parallel.HasType Φ Γ β (embed t) A :=
  Proofs.embed_hasType h

variable {ε : Type r} [HasEff Φ ε] {pureEff : ε}

/-- Every native typed equation is preserved by the embedding. -/
theorem embed_equiv {b : LetSeq.LocallyNameless.Tm ν Φ n}
    (h : LetSeq.LocallyNameless.Equiv pureEff Γ β t b A) :
    LetPar.Equiv pureEff Γ β (embed t) (embed b) A :=
  Proofs.embed_equiv h

/-- The native-to-parallel interpretation square commutes for any supplied parallel operation. -/
@[simp] theorem denote_derivation (D : τ → Type q) [ProductModel D] [UnitModel D]
    {m : Type q → Type q} [Monad m] (M : InstructionModel D Φ m) (P : ParOp m)
    (d : LetSeq.LocallyNameless.Derivation Φ Γ β t A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (derivation d).denote D M P (Control.seq D m) γ ρ = d.denote D M γ ρ :=
  Proofs.denote_derivation D M P d γ ρ

end Silmaril.Isotope.LetPar
