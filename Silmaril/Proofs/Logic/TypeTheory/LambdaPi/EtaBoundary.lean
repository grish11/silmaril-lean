module

public import Silmaril.Logic.TypeTheory.LambdaPi.Eta.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaBoundary

open Silmaril.Logic.TypeTheory.LambdaPi Silmaril.Calculi.LambdaCube

/-- The untyped η equation can forget an identity function's domain annotation. -/
theorem identity_annotations (A B : Term) :
    BetaEtaConversion (.lam A (.var 0)) (.lam B (.var 0)) := by
  have hβ : BetaEtaConversion
      (.lam A (.app ((.lam B (.var 0) : Term).rename Nat.succ) (.var 0)))
      (.lam A (.var 0)) :=
    .lam (.refl A) (.beta (B.rename Nat.succ) (.var 0) (.var 0))
  exact hβ.symm.trans (.eta A (.lam B (.var 0)))

/-- Even two β-normal annotated identities can be related by raw βη. -/
theorem beta_distinct_identities :
    ¬ Pseudo.Conv (.lam (Term.univ .type) (.var 0))
      (.lam (Term.univ .kind) (.var 0)) := by
  intro h
  have htype : Pseudo.NoRedex (.lam (Term.univ .type) (.var 0)) :=
    ⟨True.intro, True.intro⟩
  have hkind : Pseudo.NoRedex (.lam (Term.univ .kind) (.var 0)) :=
    ⟨True.intro, True.intro⟩
  have he := h.eq_of_noRedex htype hkind
  cases he

end Silmaril.Proofs.Logic.TypeTheory.LambdaPi.EtaBoundary
