module

public import Silmaril.Logic.TypeTheory.LambdaPi.Defs
public import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.Structural

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- The β-only LF profile has exactly the public syntax's β-convertibility. -/
theorem Calculus.lf_conversion_iff (declared : String → Term → Prop) (t u : Term) :
    (Calculus.lf declared).Conversion t u ↔ Silmaril.Calculi.LambdaCube.Pseudo.Conv t u :=
  ⟨Silmaril.Proofs.Logic.TypeTheory.LambdaPi.lf_conversion declared,
    Silmaril.Proofs.Logic.TypeTheory.LambdaPi.beta_conversion⟩

/-- Substitution of derived judgment hypotheses is admissible. -/
theorem Derives.bind {C : Calculus} {H K : Set Judgment}
    (hHK : ∀ J ∈ H, Derives C K J) {J : Judgment} (h : Derives C H J) : Derives C K J :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.derives_bind hHK h

/-- Adding judgment hypotheses preserves every derivation. -/
theorem Derives.mono {C : Calculus} {H K : Set Judgment} (hHK : H ⊆ K)
    {J : Judgment} (h : Derives C H J) : Derives C K J :=
  h.bind fun _ hJ => .hyp (hHK hJ)

/-- Constant translations commute with capture-avoiding variable renaming. -/
theorem Term.mapConstants_rename (f : String → String) (t : Term) (ρ : ℕ → ℕ) :
    Term.mapConstants f (t.rename ρ) = (t.mapConstants f).rename ρ :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.map_rename f t ρ

/-- Constant translations commute with simultaneous variable substitution. -/
theorem Term.mapConstants_subst (f : String → String) (t : Term) (σ : ℕ → Term) :
    Term.mapConstants f (t.subst σ) = (t.mapConstants f).subst (fun i => (σ i).mapConstants f) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.map_subst f t σ

end Silmaril.Logic.TypeTheory.LambdaPi
