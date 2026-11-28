module

public import Silmaril.SSA.Isotope.LetParCase.Defs
public import Silmaril.SSA.Isotope.LetPar.Thms
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Equiv
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Monadic
public import Silmaril.Raw.SSA.Isotope.Morphism.SeqCase.Monadic
import Silmaril.Proofs.SSA.Isotope.LetPar.LetParCase

@[expose] public section

namespace Silmaril.Isotope.LetParCase

open Parallel Semantics

universe u v w q r

variable {ν : Type v} {Φ : Type w} {n m : Nat}

/-- The embedding reflects equality of constructor trees. -/
theorem embed_injective : Function.Injective (embed : LetCase.LocallyNameless.Tm ν Φ n → Tm ν Φ n) :=
  Proofs.embed_injective

@[simp] theorem embed_rename (ρ : Fin n → Fin m) (t : LetCase.LocallyNameless.Tm ν Φ n) :
    embed (t.rename ρ) = (embed t).rename ρ :=
  Proofs.embed_rename ρ t

@[simp] theorem embed_bsubst (σ : Fin n → LetCase.LocallyNameless.Tm ν Φ m) (t : LetCase.LocallyNameless.Tm ν Φ n) :
    embed (t.bsubst σ) = (embed t).bsubst (fun i => embed (σ i)) :=
  Proofs.embed_bsubst σ t

@[simp] theorem embed_instantiate (b : LetCase.LocallyNameless.Tm ν Φ (n + 1))
    (a : LetCase.LocallyNameless.Tm ν Φ n) :
    embed (b.instantiate a) = (embed b).instantiate (embed a) :=
  Proofs.embed_instantiate b a

theorem embed_pure {ε : Type r} [HasEff Φ ε] {pureEff : ε} {t : LetCase.LocallyNameless.Tm ν Φ n}
    (h : LetCase.LocallyNameless.Pure pureEff t) : Parallel.Pure pureEff (embed t) :=
  Proofs.embed_pure h

/-- The native and parallel inclusions form a commuting square. -/
@[simp] theorem embed_seqCase (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    embed (Morphism.SeqCase.embed t) = ofLetPar (LetPar.embed t) :=
  Proofs.embed_seqCase t

/-- Adding case forms is injective on the lower parallel syntax. -/
theorem ofLetPar_injective : Function.Injective (ofLetPar : LetPar.Tm ν Φ n → Tm ν Φ n) :=
  Proofs.ofLetPar_injective

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ} {t : LetCase.LocallyNameless.Tm ν Φ n}

theorem embed_hasType (h : LetCase.LocallyNameless.HasType Φ Γ β t A) :
    Parallel.HasType Φ Γ β (embed t) A :=
  Proofs.embed_hasType h

variable {ε : Type r} [HasEff Φ ε] {pureEff : ε}

/-- Every native typed equation is preserved by the embedding. -/
theorem embed_equiv {b : LetCase.LocallyNameless.Tm ν Φ n}
    (h : LetCase.LocallyNameless.Equiv pureEff Γ β t b A) :
    LetParCase.Equiv pureEff Γ β (embed t) (embed b) A :=
  Proofs.embed_equiv h

/-- The native-to-parallel interpretation square commutes for any supplied parallel operation. -/
@[simp] theorem denote_derivation (D : τ → Type q) [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
    {m : Type q → Type q} [Monad m] (M : InstructionModel D Φ m) (P : ParOp m)
    (d : LetCase.LocallyNameless.Derivation Φ Γ β t A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (derivation d).denote D M P (Control.case D m) γ ρ = d.denote D M γ ρ :=
  Proofs.denote_derivation D M P d γ ρ

variable {a b : LetPar.Tm ν Φ n}

/-- Adding case forms preserves exact typing. -/
theorem ofLetPar_hasType (h : Parallel.HasType Φ Γ β a A) :
    Parallel.HasType Φ Γ β (ofLetPar a) A :=
  Proofs.ofLetPar_hasType h

/-- Adding case forms preserves the shared typed equations. -/
theorem ofLetPar_equiv (h : LetPar.Equiv pureEff Γ β a b A) :
    LetParCase.Equiv pureEff Γ β (ofLetPar a) (ofLetPar b) A :=
  Proofs.ofLetPar_equiv h

/-- The lower parallel interpretation is preserved in the case tier. -/
@[simp] theorem denote_ofLetParDerivation (D : τ → Type q) [ProductModel D] [UnitModel D]
    [CoproductModel D] [EmptyModel D] {m : Type q → Type q} [Monad m]
    (M : InstructionModel D Φ m) (P : ParOp m) (d : Parallel.Derivation Φ Γ β a A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (ofLetParDerivation d).denote D M P (Control.case D m) γ ρ =
      d.denote D M P (Control.seq D m) γ ρ :=
  Proofs.denote_ofLetParDerivation D M P d γ ρ

/-- Lift a pure case scrutinee out of the left parallel branch. -/
theorem parCaseLeft {e t : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {X Y B : τ}
    (hp : Parallel.Pure pureEff e) (he : Parallel.HasType Φ Γ β e (coprod X Y))
    (hl : Parallel.HasType Φ Γ (.snoc β X) l A) (hr : Parallel.HasType Φ Γ (.snoc β Y) r A)
    (ht : Parallel.HasType Φ Γ β t B) :
    LetParCase.Equiv pureEff Γ β (.par (.case hasCase e l r) t)
      (.case hasCase e (.par l t.lift) (.par r t.lift)) (product A B) :=
  Proofs.parCaseLeft hp he hl hr ht

/-- Lift a pure case scrutinee out of the right parallel branch. -/
theorem parCaseRight {e t : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {X Y B : τ}
    (hp : Parallel.Pure pureEff e) (he : Parallel.HasType Φ Γ β e (coprod X Y))
    (hl : Parallel.HasType Φ Γ (.snoc β X) l B) (hr : Parallel.HasType Φ Γ (.snoc β Y) r B)
    (ht : Parallel.HasType Φ Γ β t A) :
    LetParCase.Equiv pureEff Γ β (.par t (.case hasCase e l r))
      (.case hasCase e (.par t.lift l) (.par t.lift r)) (product A B) :=
  Proofs.parCaseRight hp he hl hr ht

end Silmaril.Isotope.LetParCase
