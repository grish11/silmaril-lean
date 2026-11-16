module

public import Silmaril.Logic.TypeTheory.LambdaPi.Eta.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.Generation.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaTyping

open Silmaril.Logic.TypeTheory.LambdaPi Silmaril.Calculi.LambdaCube

/-- Weakening beneath the product binder followed by its fresh variable cancels. -/
theorem codomain_fresh (B : Term) :
    (B.rename (Silmaril.DeBruijn.lift Nat.succ)).substOne (.var 0) = B := by
  rw [Pseudo.substOne, Pseudo.subst_rename]
  apply Pseudo.subst_var
  intro i
  cases i <;> rfl

theorem product_type_formation {C : Calculus} {Γ : List Term} {f A B : Term}
    (hf : Derives C ∅ ⟨Γ, f, .pi A B⟩) :
    ∃ s, Derives C ∅ ⟨Γ, .pi A B, Term.univ s⟩ := by
  rcases hf.typeCorrectness with he | hs
  · cases he
  · exact hs

theorem application_typed {C : Calculus} {Γ : List Term} {f A B : Term}
    (hf : Derives C ∅ ⟨Γ, f, .pi A B⟩) :
    Derives C ∅ ⟨A :: Γ, .app (f.rename Nat.succ) (.var 0), B⟩ := by
  obtain ⟨_, hPi⟩ := product_type_formation hf
  obtain ⟨hA, _, _⟩ := hPi.productFormation
  have hbody := Derives.app (Derives.weak hf hA) (Derives.var hA)
  simpa only [codomain_fresh] using hbody

theorem expansion_typed {C : Calculus} {Γ : List Term} {f A B : Term}
    (hf : Derives C ∅ ⟨Γ, f, .pi A B⟩) :
    Derives C ∅ ⟨Γ, .lam A (.app (f.rename Nat.succ) (.var 0)), .pi A B⟩ := by
  obtain ⟨_, hPi⟩ := product_type_formation hf
  exact .lam (application_typed hf) hPi

theorem conversion_iff_pointwise (C : Calculus) (f g : Term) :
    C.withEta.Conversion f g ↔
      C.withEta.Conversion (.app (f.rename Nat.succ) (.var 0))
        (.app (g.rename Nat.succ) (.var 0)) := by
  constructor
  · intro h
    exact .app (h.rename Nat.succ) (.refl _)
  · intro h
    exact (C.eta (Term.univ .type) f).symm.trans
      ((Calculus.Conversion.lam (.refl (Term.univ .type)) h).trans
        (C.eta (Term.univ .type) g))

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaTyping
