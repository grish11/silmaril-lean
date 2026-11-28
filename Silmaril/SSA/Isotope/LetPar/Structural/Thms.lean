module

public import Silmaril.SSA.Isotope.LetPar.Equations.Defs
public import Silmaril.SSA.Isotope.LetPar.Interpretation.Defs
import Silmaril.Proofs.SSA.Isotope.LetPar.Structural

@[expose] public section

namespace Silmaril.Isotope.Parallel

universe u v w x

variable {tier target : Tier} {ν : Type v} {Φ : Type w} {n m : Nat}

namespace Tm

/-- A tier inclusion is injective on constructor trees. -/
theorem widen_injective (h : Tier.Inclusion tier target) :
    Function.Injective (widen h : Tm tier ν Φ n → _) :=
  Proofs.Tm.widen_injective h

@[simp] theorem widen_rename (h : Tier.Inclusion tier target) (ρ : Fin n → Fin m)
    (t : Tm tier ν Φ n) :
    (t.rename ρ).widen h = (t.widen h).rename ρ :=
  Proofs.Tm.widen_rename h ρ t

@[simp] theorem widen_bsubst (h : Tier.Inclusion tier target) (σ : Fin n → Tm tier ν Φ m)
    (t : Tm tier ν Φ n) :
    (t.bsubst σ).widen h = (t.widen h).bsubst (fun i => (σ i).widen h) :=
  Proofs.Tm.widen_bsubst h σ t

@[simp] theorem widen_instantiate (h : Tier.Inclusion tier target) (b : Tm tier ν Φ (n + 1))
    (a : Tm tier ν Φ n) :
    (b.instantiate a).widen h = (b.widen h).instantiate (a.widen h) :=
  Proofs.Tm.widen_instantiate h b a

end Tm

namespace Pure

theorem widen {ε : Type x} [HasEff Φ ε] {pureEff : ε} {t : Tm tier ν Φ n}
    (h : Tier.Inclusion tier target) (hp : Pure pureEff t) : Pure pureEff (t.widen h) :=
  Proofs.pure_widen h hp

end Pure

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
  [DecidableEq ν] [HasTy Φ τ] {Γ : Ctx ν τ}

namespace HasType

variable {β : BoundCtx τ n} {a : Tm tier ν Φ n} {A B : τ}

theorem rename {β' : BoundCtx τ m} (ρ : BoundCtx.Renaming β β')
    (h : HasType Φ Γ β a A) : HasType Φ Γ β' (a.rename ρ.toFun) A :=
  Proofs.hasType_rename ρ h

theorem lift (h : HasType Φ Γ β a A) : HasType Φ Γ (.snoc β B) a.lift A :=
  rename (BoundCtx.Renaming.succ β B) h

theorem underBinder {f : Tm tier ν Φ (n + 1)} {C : τ}
    (h : HasType Φ Γ (.snoc β B) f C) :
    HasType Φ Γ (.snoc (.snoc β A) B) f.underBinder C :=
  rename (BoundCtx.Renaming.underBinder β A B) h

theorem leftResult {f : Tm tier ν Φ (n + 1)} {C : τ}
    (h : HasType Φ Γ (.snoc β A) f C) :
    HasType Φ Γ (.snoc (.snoc β A) B) f.leftResult C :=
  rename ⟨_, Fin.cases rfl (fun _ => rfl)⟩ h

end HasType

end Silmaril.Isotope.Parallel
