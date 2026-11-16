module

public import Silmaril.Logic.HybridPolyadic.Defs

public section
namespace Silmaril.Proofs.Logic.HybridPolyadic
open Silmaril.Logic.HybridPolyadic

private theorem cons_comp {n m : ℕ} {W : Type} (ρ : Fin n → Fin m)
    (env : Fin m → W) (w : W) :
    Fin.cons w env ∘ liftRename ρ = Fin.cons w (env ∘ ρ) := by
  funext i
  cases i using Fin.cases <;> rfl

private theorem map_cons {n : ℕ} {W V : Type} (f : W → V) (env : Fin n → W) (w : W) :
    f ∘ Fin.cons w env = Fin.cons (f w) (f ∘ env) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem holds_rename {S : Signature} (M : Model S) {n m : ℕ} (ρ : Fin n → Fin m)
    (p : Formula S n) (env : Fin m → M.World) (w : M.World) :
    (p.rename ρ).Holds M env w ↔ p.Holds M (env ∘ ρ) w := by
  induction p generalizing m w with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => exact imp_congr (hp ρ env w) (hq ρ env w)
  | nominal _ => rfl
  | state _ => rfl
  | atNom a p hp => exact hp ρ env (M.name a)
  | atState i p hp => exact hp ρ env (env (ρ i))
  | dia a ps ih =>
    exact exists_congr fun vs => and_congr Iff.rfl (forall_congr' fun i => ih i ρ env (vs i))
  | down p hp =>
    change (p.rename (liftRename ρ)).Holds M (Fin.cons w env) w ↔ _
    rw [hp, cons_comp]
    rfl

theorem holds_map {S T : Signature} (f : S ⟶ T) (M : Model T) {n : ℕ}
    (p : Formula S n) (env : Fin n → M.World) (w : M.World) :
    (p.map f).Holds M env w ↔ p.Holds ((reduct f).obj M) env w := by
  induction p generalizing w with
  | atom _ => rfl
  | bot => rfl
  | imp p q hp hq => exact imp_congr (hp env w) (hq env w)
  | nominal _ => rfl
  | state _ => rfl
  | atNom a p hp => exact hp env (M.name (f.nominal a))
  | atState i p hp => exact hp env (env i)
  | dia a ps ih =>
    exact exists_congr fun vs => and_congr Iff.rfl (forall_congr' fun i => ih i env (vs i))
  | down p hp => exact hp (Fin.cons w env) w

/-- Injectivity is used precisely for the nominal and state-equality tests. -/
theorem holds_hom {S : Signature} {M N : Model S} (h : M ⟶ N) {n : ℕ}
    (p : Formula S n) (env : Fin n → M.World) (w : M.World) :
    p.Holds M env w ↔ p.Holds N (h.map ∘ env) (h.map w) := by
  induction p generalizing w with
  | atom a => exact h.atoms a w
  | bot => rfl
  | imp p q hp hq => exact imp_congr (hp env w) (hq env w)
  | nominal a =>
    change w = M.name a ↔ h.map w = N.name a
    have hname : h.map (M.name a) = N.name a := h.names a
    rw [← hname]
    exact h.injective.eq_iff.symm
  | state i => exact h.injective.eq_iff.symm
  | atNom a p hp =>
    change p.Holds M env (M.name a) ↔ p.Holds N (h.map ∘ env) (N.name a)
    rw [← h.names a]
    exact hp env (M.name a)
  | atState i p hp => exact hp env (env i)
  | dia a ps ih =>
    show (∃ vs, M.relation _ a w vs ∧ ∀ i, (ps i).Holds M env (vs i)) ↔ _
    constructor
    · rintro ⟨vs, hv, hs⟩
      exact ⟨h.map ∘ vs, h.forth _ a w vs hv, fun i => (ih i env (vs i)).mp (hs i)⟩
    · rintro ⟨vs, hv, hs⟩
      obtain ⟨us, hu, heq⟩ : ∃ us, M.relation _ a w us ∧ h.map ∘ us = vs := h.back _ a w vs hv
      have hs' : ∀ i, (ps i).Holds N (h.map ∘ env) ((h.map ∘ us) i) := by
        rw [heq]
        exact hs
      exact ⟨us, hu, fun i => (ih i env (us i)).mpr (hs' i)⟩
  | down p hp =>
    change p.Holds M (Fin.cons w env) w ↔ _
    rw [hp, map_cons]
    rfl

end Silmaril.Proofs.Logic.HybridPolyadic
