module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ

public section

/-!
# Confluence for the separately named left-linear J extension

A complete-development triangle gives the parallel diamond and confluence.
Every original directed step embeds, but this extension has strictly more
raw directed computations. Neither conversion conservativity nor checked
typing preservation for arbitrary extended steps is asserted.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ

/-- Every full-syntax term admits the reflexive parallel development. -/
theorem Parallel.rfl {n : ℕ} (t : Term n) : Parallel t t :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.Parallel.rfl t

/-- Renaming preserves the extended parallel relation. -/
theorem Parallel.rename {n : ℕ} {t u : Term n} (h : Parallel t u)
    {m : ℕ} (ρ : Fin n → Fin m) : Parallel (t.rename ρ) (u.rename ρ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.Parallel.rename h ρ

/-- Pointwise parallel substitutions preserve parallel contraction. -/
theorem Parallel.subst {n : ℕ} {t u : Term n} (h : Parallel t u)
    {m : ℕ} {σ τ : Fin n → Term m} (hσ : ∀ i, Parallel (σ i) (τ i)) :
    Parallel (t.subst σ) (u.subst τ) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.Parallel.subst h hσ

/-- Parallel beta substitution permits both body and argument to develop. -/
theorem Parallel.instantiate {n : ℕ} {t u : Term (n + 1)} {a b : Term n}
    (h : Parallel t u) (ha : Parallel a b) : Parallel (t.instantiate a) (u.instantiate b) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.Parallel.instantiate h ha

/-- Every parallel reduct develops to the source complete development. -/
theorem Parallel.triangle {n : ℕ} {t u : Term n} (h : Parallel t u) : Parallel u (develop t) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.Parallel.triangle h

/-- Two parallel developments have a common parallel successor. -/
theorem Parallel.diamond {n : ℕ} {t u v : Term n} (hu : Parallel t u) (hv : Parallel t v) :
    ∃ w, Parallel u w ∧ Parallel v w :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.Parallel.diamond hu hv

/-- Finite directed computations in the left-linear extension are confluent. -/
theorem confluent {n : ℕ} {t u v : Term n} (hu : Reduces t u) (hv : Reduces t v) :
    Relation.Join (@Reduces n) u v :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.confluent hu hv

/-- Extended conversion is exactly existence of an extended common reduct. -/
theorem convertible_iff_join {n : ℕ} {t u : Term n} :
    Convertible t u ↔ Relation.Join (@Reduces n) t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.convertible_iff_join

/-- Each exact original primitive root law embeds into the extension. -/
theorem ofRootReduction {n : ℕ} {t u : Term n} (h : RootReduction t u) : Parallel t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.root_toParallel h

/-- Every original compatible directed step embeds into parallel contraction. -/
theorem ofReductionStep {n : ℕ} {t u : Term n} (h : ReductionStep t u) : Parallel t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.step_toParallel h

/-- Original directed paths remain directed paths in the extension. -/
theorem ofReduces {n : ℕ} {t u : Term n}
    (h : Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduces t u) : Reduces t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.original_reduces h

/-- Original conversion embeds into the separately named extended conversion. -/
theorem ofConvertible {n : ℕ} {t u : Term n}
    (h : Silmaril.Logic.TypeTheory.IntensionalMLTT.Convertible t u) : Convertible t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.original_convertible h

/-- A closed raw witness proves strictness of the directed extension. -/
theorem strict_directed_extension : ∃ t u : Term 0,
    Reduces t u ∧ ¬ Silmaril.Logic.TypeTheory.IntensionalMLTT.Reduces t u :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.LinearJ.strict_directed_extension

end Silmaril.Logic.TypeTheory.IntensionalMLTT.LinearJ
