module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Substitution.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution

public section

/-!
# Admissible intensional substitution

Renaming and simultaneous substitution preserve actual typing derivations,
including cumulative universes and both binders of based J. The hypotheses
are a well-formed target telescope and syntactically typed assignments.
These results do not assume or establish semantic soundness, subject reduction
for arbitrary raw conversion, or normalization.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

namespace Conversion

/-- Capture-avoiding renaming preserves every beta conversion constructor. -/
noncomputable def rename {n : ℕ} {t u : Term n} (h : Conversion t u)
    {m : ℕ} (ρ : Fin n → Fin m) : Conversion (t.rename ρ) (u.rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.conversion_rename h ρ

/-- Capture-avoiding simultaneous substitution preserves beta conversion. -/
noncomputable def subst {n : ℕ} {t u : Term n} (h : Conversion t u)
    {m : ℕ} (σ : Fin n → Term m) : Conversion (t.subst σ) (u.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.conversion_subst h σ

end Conversion

namespace Renaming

/-- Extending both telescopes extends a type-respecting renaming. -/
theorem lift {n m : ℕ} {Γ : Context n} {Δ : Context m} {ρ : Fin n → Fin m}
    (hρ : Renaming Γ Δ ρ) (A : Term n) :
    Renaming (Γ.snoc A) (Δ.snoc (A.rename ρ)) (Term.upRen ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.renaming_lift hρ A

/-- Ordinary scope extension respects every declaration lookup. -/
theorem weaken {n : ℕ} (Γ : Context n) (A : Term n) : Renaming Γ (Γ.snoc A) Fin.succ :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.renaming_weaken Γ A

end Renaming

namespace Derivation

/-- Any context-respecting renaming transports a complete typing tree. -/
noncomputable def rename {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Derivation Γ t A) {m : ℕ} {Δ : Context m} (hΔ : ContextDerivation Δ)
    (ρ : Fin n → Fin m) (hρ : Renaming Γ Δ ρ) :
    Derivation Δ (t.rename ρ) (A.rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.derivation_rename h hΔ ρ hρ

/-- Weakening is admissible for the entire intensional calculus. -/
noncomputable def weaken {n i : ℕ} {Γ : Context n} {t A B : Term n}
    (h : Derivation Γ t A) (hΓ : ContextDerivation Γ) (hB : Derivation Γ B (.univ i)) :
    Derivation (Γ.snoc B) t.weaken A.weaken :=
  h.rename (.snoc hΓ hB) Fin.succ (Renaming.weaken Γ B)

/-- Simultaneous substitution transports a complete typing tree. -/
noncomputable def subst {n : ℕ} {Γ : Context n} {t A : Term n}
    (h : Derivation Γ t A) {m : ℕ} {Δ : Context m} (hΔ : ContextDerivation Δ)
    (σ : Fin n → Term m) (hσ : Substitution Γ Δ σ) :
    Derivation Δ (t.subst σ) (A.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.derivation_subst h hΔ σ hσ

/-- Substitution for the newest declaration has the usual dependent result type. -/
noncomputable def instantiate {n : ℕ} {Γ : Context n} {A a : Term n}
    {t B : Term (n + 1)} (ht : Derivation (Γ.snoc A) t B)
    (hΓ : ContextDerivation Γ) (ha : Derivation Γ a A) :
    Derivation Γ (t.instantiate a) (B.instantiate a) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.derivation_instantiate ht hΓ ha

end Derivation

namespace Substitution

/-- Variables themselves form a typed identity substitution. -/
noncomputable def identity {n : ℕ} {Γ : Context n} (hΓ : ContextDerivation Γ) :
    Substitution Γ Γ Term.var :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.substitution_id hΓ

/-- Assigning a typed term extends a simultaneous substitution at the source. -/
noncomputable def cons {n m : ℕ} {Γ : Context n} {Δ : Context m}
    {σ : Fin n → Term m} {A : Term n} {a : Term m}
    (hσ : Substitution Γ Δ σ) (ha : Derivation Δ a (A.subst σ)) :
    Substitution (Γ.snoc A) Δ (Fin.cons a σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.substitution_cons hσ ha

end Substitution

/-- Typed beta equality is stable under syntactically typed substitutions. -/
theorem TypedEq.subst {n m : ℕ} {Γ : Context n} {Δ : Context m} {t u A : Term n}
    (h : TypedEq Γ t u A) (hΔ : ContextDerivation Δ) (σ : Fin n → Term m)
    (hσ : Substitution Γ Δ σ) : TypedEq Δ (t.subst σ) (u.subst σ) (A.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.typedEq_subst h hΔ σ hσ

/-- Lambda beta computation has a derived typing for its substituted endpoint. -/
theorem TypedEq.beta {n i j : ℕ} {Γ : Context n} {A a : Term n}
    {B body : Term (n + 1)} (hΓ : ContextDerivation Γ)
    (hA : Derivation Γ A (.univ i)) (hB : Derivation (Γ.snoc A) B (.univ j))
    (ht : Derivation (Γ.snoc A) body B) (ha : Derivation Γ a A) :
    TypedEq Γ (.app (.lam A body) a) (body.instantiate a) (B.instantiate a) :=
  ⟨⟨.app (.lam hA hB ht) ha⟩, ⟨ht.instantiate hΓ ha⟩, ⟨.beta A body a⟩⟩

namespace Term

/-- Capture-avoiding rename weaken for the complete scoped syntax. -/
theorem rename_weaken {n m : ℕ} (t : Term n) (ρ : Fin n → Fin m) :
    t.weaken.rename (Term.upRen ρ) = (t.rename ρ).weaken :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.rename_weaken t ρ

/-- Capture-avoiding subst weaken for the complete scoped syntax. -/
theorem subst_weaken {n m : ℕ} (t : Term n) (σ : Fin n → Term m) :
    t.weaken.subst (Term.upSub σ) = (t.subst σ).weaken :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.subst_weaken t σ

/-- Capture-avoiding rename instantiate for the complete scoped syntax. -/
theorem rename_instantiate {n m : ℕ} (t : Term (n + 1)) (a : Term n)
    (ρ : Fin n → Fin m) :
    (t.instantiate a).rename ρ = (t.rename (Term.upRen ρ)).instantiate (a.rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.rename_instantiate t a ρ

/-- Capture-avoiding subst instantiate for the complete scoped syntax. -/
theorem subst_instantiate {n m : ℕ} (t : Term (n + 1)) (a : Term n)
    (σ : Fin n → Term m) :
    (t.instantiate a).subst σ = (t.subst (Term.upSub σ)).instantiate (a.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.subst_instantiate t a σ

/-- Capture-avoiding rename instantiate₂ for the complete scoped syntax. -/
theorem rename_instantiate₂ {n m : ℕ} (t : Term (n + 2)) (a p : Term n)
    (ρ : Fin n → Fin m) :
    (t.instantiate₂ a p).rename ρ =
      (t.rename (Term.upRen (Term.upRen ρ))).instantiate₂ (a.rename ρ) (p.rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.rename_instantiate₂ t a p ρ

/-- Capture-avoiding subst instantiate₂ for the complete scoped syntax. -/
theorem subst_instantiate₂ {n m : ℕ} (t : Term (n + 2)) (a p : Term n)
    (σ : Fin n → Term m) :
    (t.instantiate₂ a p).subst σ =
      (t.subst (Term.upSub (Term.upSub σ))).instantiate₂ (a.subst σ) (p.subst σ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.subst_instantiate₂ t a p σ

/-- Capture-avoiding rename natStepType for the complete scoped syntax. -/
theorem rename_natStepType {n m : ℕ} (C : Term (n + 1)) (ρ : Fin n → Fin m) :
    C.natStepType.rename ρ = (C.rename (Term.upRen ρ)).natStepType :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.rename_natStepType C ρ

/-- Capture-avoiding subst natStepType for the complete scoped syntax. -/
theorem subst_natStepType {n m : ℕ} (C : Term (n + 1)) (σ : Fin n → Term m) :
    C.natStepType.subst σ = (C.subst (Term.upSub σ)).natStepType :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.subst_natStepType C σ

end Term

namespace Renaming

/-- Compose two declaration-preserving renamings. -/
theorem comp {n m k : ℕ} {Γ : Context n} {Δ : Context m} {Θ : Context k}
    {ρ : Fin n → Fin m} {τ : Fin m → Fin k}
    (hρ : Renaming Γ Δ ρ) (hτ : Renaming Δ Θ τ) : Renaming Γ Θ (τ ∘ ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.Substitution.renaming_comp hρ hτ

end Renaming

end Silmaril.Logic.TypeTheory.IntensionalMLTT
