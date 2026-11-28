module

public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Extensional
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Normalize
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Trace

public section

namespace Silmaril.Isotope.LetCase.Structural.Finite

open LocallyNameless (Derivation Equiv Tm)
open Reply (Γ₀ run)
open Silmaril.Isotope.Semantics (BoundEnv)
open scoped Silmaril.Isotope.LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [Signature Φ]
set_option backward.isDefEq.respectTransparency false

private theorem normalize_closed {t : Term Φ 0} {A : Types} (d : Derivation Φ Γ₀ .nil t A) :
    Normalizes A t := by
  let ρ : Assignment (.nil : Context 0) := fun i => i.elim0
  have result := normalize_proof d ρ
  have identity : ρ.terms (Φ := Φ) = Tm.bv := funext (fun i => i.elim0)
  rwa [identity, Tm.bsubst_id] at result

private theorem reflect_closed {t u : Term Φ 0} {A : Types}
    (d : Derivation Φ Γ₀ .nil t A) (e : Derivation Φ Γ₀ .nil u A)
    (eq : run d closedEnv = run e closedEnv) : Equiv false Γ₀ .nil t u A := by
  obtain ⟨_, p, hp⟩ := normalize_closed d
  obtain ⟨_, q, hq⟩ := normalize_closed e
  have heads := (run_of_equiv d p.typing hp closedEnv).symm.trans
    (eq.trans (run_of_equiv e q.typing hq closedEnv))
  exact hp.trans ((p.reflect_proof q heads).trans hq.symm)

private theorem reflect_slot {n : Nat} {β : Context n} {t u : Term Φ (n + 1)} {X D : Types}
    (reflect : ∀ {t u : Term Φ n}, (d : Derivation Φ Γ₀ β t D) → (e : Derivation Φ Γ₀ β u D) →
      (∀ ρ : BoundEnv Value β, run d ρ = run e ρ) → Equiv false Γ₀ β t u D)
    (d : Derivation Φ Γ₀ (β.snoc X) t D) (e : Derivation Φ Γ₀ (β.snoc X) u D)
    (eq : ∀ ρ : BoundEnv Value (β.snoc X), run d ρ = run e ρ) :
    Equiv false Γ₀ (β.snoc X) t u D := by
  apply constructor_ext_type_proof X d.toHasType e.toHasType
  intro x
  obtain ⟨dx⟩ := Derivation.ofHasType (d.toHasType.instantiate x.typing.toHasType)
  obtain ⟨ex⟩ := Derivation.ofHasType (e.toHasType.instantiate x.typing.toHasType)
  apply reflect dx ex
  intro ρ
  exact (run_instantiate d x dx (.refl dx.toHasType) ρ).symm.trans
    ((eq (ρ.snoc x.value)).trans (run_instantiate e x ex (.refl ex.toHasType) ρ))

theorem reflect_open_proof {n : Nat} {β : Context n} {t u : Term Φ n} {A : Types}
    (input : StructuralContext β) (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A)
    (eq : ∀ ρ : BoundEnv Value β, run d ρ = run e ρ) : Equiv false Γ₀ β t u A := by
  induction input with
  | nil => exact reflect_closed d e (eq closedEnv)
  | snoc _ _ ih => exact reflect_slot (fun d₀ e₀ eq₀ => ih d₀ e₀ eq₀) d e eq

theorem reflect_snoc_proof {n : Nat} {β : Context n} {t u : Term Φ (n + 1)} {X D : Types}
    (input : StructuralContext β) (d : Derivation Φ Γ₀ (β.snoc X) t D)
    (e : Derivation Φ Γ₀ (β.snoc X) u D)
    (eq : ∀ ρ : BoundEnv Value (β.snoc X), run d ρ = run e ρ) :
    Equiv false Γ₀ (β.snoc X) t u D :=
  reflect_slot (reflect_open_proof input) d e eq

end Silmaril.Isotope.LetCase.Structural.Finite
