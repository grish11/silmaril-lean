module

public import Silmaril.Logic.TypeTheory.LambdaPi.Generation.Defs
public import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.Generation

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- Inserting a domain beneath the newest binder preserves a closed typing derivation. -/
theorem Derives.weakenBeneath {C : Calculus} {Γ : List Term} {A b B D : Term}
    (h : Derives C ∅ ⟨A :: Γ, b, B⟩) (hA : Derives C ∅ ⟨Γ, A, Term.univ .type⟩)
    (hD : Derives C ∅ ⟨Γ, D, Term.univ .type⟩) :
    Derives C ∅ ⟨A.rename Nat.succ :: D :: Γ,
      b.rename (Silmaril.DeBruijn.lift Nat.succ), B.rename (Silmaril.DeBruijn.lift Nat.succ)⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.weaken_beneath h hA hD

/-- A derived product has an actually formed domain and codomain, including after conversion. -/
theorem Derives.productFormation {C : Calculus} {Γ : List Term} {A B T : Term}
    (h : Derives C ∅ ⟨Γ, .pi A B, T⟩) :
    Derives C ∅ ⟨Γ, A, Term.univ .type⟩ ∧
      ∃ s, Derives C ∅ ⟨A :: Γ, B, Term.univ s⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.product_formation h A B rfl

/-- A closed derivation's type is `Kind` or has an actual sort derivation. -/
theorem Derives.typeCorrectness {C : Calculus} {J : Judgment} (h : Derives C ∅ J) :
    J.type = Term.univ .kind ∨ ∃ s, Derives C ∅ ⟨J.context, J.type, Term.univ s⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.type_correctness h

/-- Application inversion recovers actual premises, result conversion and target formation. -/
theorem Derives.applicationGeneration {C : Calculus} {Γ : List Term} {f a T : Term}
    (h : Derives C ∅ ⟨Γ, .app f a, T⟩) :
    ∃ A B, Derives C ∅ ⟨Γ, f, .pi A B⟩ ∧
      Derives C ∅ ⟨Γ, a, A⟩ ∧ C.Conversion (B.substOne a) T ∧
      ∃ s, Derives C ∅ ⟨Γ, T, Term.univ s⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.application_generation h f a rfl

/-- Abstraction inversion recovers its annotated domain rather than a convertible substitute. -/
theorem Derives.abstractionGeneration {C : Calculus} {Γ : List Term} {A b T : Term}
    (h : Derives C ∅ ⟨Γ, .lam A b, T⟩) :
    ∃ B s, Derives C ∅ ⟨A :: Γ, b, B⟩ ∧
      Derives C ∅ ⟨Γ, .pi A B, Term.univ s⟩ ∧ C.Conversion (.pi A B) T ∧
      ∃ r, Derives C ∅ ⟨Γ, T, Term.univ r⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.abstraction_generation h A b rfl

/-- β-only LF has product compatibility for every constant declaration relation. -/
theorem Calculus.lf_productCompatible (declared : String → Term → Prop) :
    (Calculus.lf declared).ProductCompatible :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.beta_product_compatible declared

/-- Head β contraction preserves the original result type under product compatibility.

The input may use arbitrary weakening and conversion derivations. Rewrite presentations
must establish the displayed compatibility condition separately.
-/
theorem Derives.headBeta {C : Calculus} (hC : C.ProductCompatible)
    {Γ : List Term} {A b a T : Term}
    (h : Derives C ∅ ⟨Γ, .app (.lam A b) a, T⟩) :
    Derives C ∅ ⟨Γ, b.substOne a, T⟩ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.head_beta_subject_reduction hC h

/-- Head β contraction is type preserving in every β-only LF signature. -/
theorem Derives.lf_headBeta {declared : String → Term → Prop}
    {Γ : List Term} {A b a T : Term}
    (h : Derives (Calculus.lf declared) ∅ ⟨Γ, .app (.lam A b) a, T⟩) :
    Derives (Calculus.lf declared) ∅ ⟨Γ, b.substOne a, T⟩ :=
  h.headBeta (Calculus.lf_productCompatible declared)

end Silmaril.Logic.TypeTheory.LambdaPi
