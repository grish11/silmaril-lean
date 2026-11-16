module

public import Silmaril.Logic.ModalMu.Defs
public import Mathlib.Tactic.Tauto

@[expose] public section
namespace Silmaril.Logic.ModalMu
open CategoryTheory Silmaril.Logic.Institution
variable {n : Nat}

 theorem Formula.map_id {S : Signature} (p : Formula S n) : p.map (𝟙 S) = p := by
  induction p <;> simp_all [Formula.map] <;> rfl

theorem Formula.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
    (p : Formula S n) : p.map (f ≫ g) = (p.map f).map g := by
  induction p <;> simp_all [Formula.map] <;> rfl

theorem Formula.dual_dual {S : Signature} (p : Formula S n) : p.dual.dual = p := by
  induction p <;> simp_all [Formula.dual]

/-- A syntactic body induces a monotone set transformer, including nested binders. -/
noncomputable def bodyMap {S : Signature} (M : Model S) (p : Formula S (n + 1))
    (ρ : Env M.World n) : Set M.World →o Set M.World := (p.denote M).comp (insert ρ)

theorem Formula.mu_unfold {S : Signature} (M : Model S) (p : Formula S (n + 1))
    (ρ : Env M.World n) :
    (Formula.mu p).denote M ρ = p.denote M (extend ρ ((Formula.mu p).denote M ρ)) :=
  (bodyMap M p ρ).map_lfp.symm

theorem Formula.nu_unfold {S : Signature} (M : Model S) (p : Formula S (n + 1))
    (ρ : Env M.World n) :
    (Formula.nu p).denote M ρ = p.denote M (extend ρ ((Formula.nu p).denote M ρ)) :=
  (bodyMap M p ρ).map_gfp.symm

theorem Formula.mu_le {S : Signature} (M : Model S) (p : Formula S (n + 1))
    (ρ : Env M.World n) (X : Set M.World) (h : p.denote M (extend ρ X) ⊆ X) :
    (Formula.mu p).denote M ρ ⊆ X := (bodyMap M p ρ).lfp_le h

theorem Formula.le_nu {S : Signature} (M : Model S) (p : Formula S (n + 1))
    (ρ : Env M.World n) (X : Set M.World) (h : X ⊆ p.denote M (extend ρ X)) :
    X ⊆ (Formula.nu p).denote M ρ := (bodyMap M p ρ).le_gfp h

theorem Formula.denote_map {S T : Signature} (f : S ⟶ T) (M : Model T)
    (p : Formula S n) : (p.map f).denote M = p.denote (reduct f M) := by
  apply OrderHom.ext
  funext ρ
  induction p with
  | pos a => rfl
  | neg a => rfl
  | bot => rfl
  | top => rfl
  | var i => rfl
  | conj p q hp hq =>
      change (p.map f).denote M ρ ∩ (q.map f).denote M ρ =
        p.denote (reduct f M) ρ ∩ q.denote (reduct f M) ρ
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      change (p.map f).denote M ρ ∪ (q.map f).denote M ρ =
        p.denote (reduct f M) ρ ∪ q.denote (reduct f M) ρ
      rw [hp, hq]
      rfl
  | box a p hp =>
      change {w | ∀ v, M.step (f.action a) w v → v ∈ (p.map f).denote M ρ} =
        {w | ∀ v, M.step (f.action a) w v → v ∈ p.denote (reduct f M) ρ}
      rw [hp]
      rfl
  | diamond a p hp =>
      change {w | ∃ v, M.step (f.action a) w v ∧ v ∈ (p.map f).denote M ρ} =
        {w | ∃ v, M.step (f.action a) w v ∧ v ∈ p.denote (reduct f M) ρ}
      rw [hp]
      rfl
  | mu p hp =>
      change ((p.map f).denote M |>.comp (insert ρ)).lfp =
        ((p.denote (reduct f M)).comp (insert ρ)).lfp
      congr 1
      apply OrderHom.ext
      funext X
      exact hp (extend ρ X)
  | nu p hp =>
      change ((p.map f).denote M |>.comp (insert ρ)).gfp =
        ((p.denote (reduct f M)).comp (insert ρ)).gfp
      congr 1
      apply OrderHom.ext
      funext X
      exact hp (extend ρ X)


/-- Complement conjugation exchanges actual least and greatest fixed points. -/
theorem gfp_complement_lfp {W : Type} (F G : Set W →o Set W)
    (h : ∀ X, G X = (F Xᶜ)ᶜ) : G.gfp = (F.lfp)ᶜ := by
  classical
  apply Set.Subset.antisymm
  · have hf : F (G.gfp)ᶜ ⊆ (G.gfp)ᶜ := by
      intro w hw hg
      have ht : w ∈ G G.gfp := by rw [G.map_gfp]; exact hg
      rw [h] at ht
      exact ht hw
    intro w hw hl
    exact (F.lfp_le hf hl) hw
  · apply G.le_gfp
    rw [h, compl_compl, F.map_lfp]

theorem lfp_complement_gfp {W : Type} (F G : Set W →o Set W)
    (h : ∀ X, G X = (F Xᶜ)ᶜ) : G.lfp = (F.gfp)ᶜ := by
  classical
  have hs : ∀ X, F X = (G Xᶜ)ᶜ := by
    intro X
    rw [h, compl_compl, compl_compl]
  have he := gfp_complement_lfp G F hs
  rw [he, compl_compl]

/-- Duality complements all free-variable valuations as well as formula truth. -/
theorem Formula.denote_dual {S : Signature} (M : Model S) (p : Formula S n)
    (ρ : Env M.World n) : p.dual.denote M (fun i => (ρ i)ᶜ) = (p.denote M ρ)ᶜ := by
  classical
  induction p with
  | pos a => rfl
  | neg a =>
      ext w
      change w ∈ M.valuation a ↔ ¬ ¬ w ∈ M.valuation a
      tauto
  | bot => exact Set.compl_empty.symm
  | top => exact Set.compl_univ.symm
  | var i => rfl
  | conj p q hp hq =>
      change p.dual.denote M _ ∪ q.dual.denote M _ = (p.denote M ρ ∩ q.denote M ρ)ᶜ
      rw [hp, hq]
      exact (Set.compl_inter _ _).symm
  | disj p q hp hq =>
      change p.dual.denote M _ ∩ q.dual.denote M _ = (p.denote M ρ ∪ q.denote M ρ)ᶜ
      rw [hp, hq]
      exact (Set.compl_union _ _).symm
  | box a p hp =>
      change {w | ∃ v, M.step a w v ∧ v ∈ p.dual.denote M _} =
        {w | ∀ v, M.step a w v → v ∈ p.denote M ρ}ᶜ
      rw [hp]
      ext w
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, exists_prop]
  | diamond a p hp =>
      change {w | ∀ v, M.step a w v → v ∈ p.dual.denote M _} =
        {w | ∃ v, M.step a w v ∧ v ∈ p.denote M ρ}ᶜ
      rw [hp]
      ext w
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_and]
  | mu p hp =>
      show ((p.dual.denote M).comp (insert (fun i => (ρ i)ᶜ))).gfp =
        (((p.denote M).comp (insert ρ)).lfp)ᶜ
      apply gfp_complement_lfp
      intro X
      change p.dual.denote M (extend (fun i => (ρ i)ᶜ) X) =
        (p.denote M (extend ρ Xᶜ))ᶜ
      have he : extend (fun i => (ρ i)ᶜ) X = fun i => (extend ρ Xᶜ i)ᶜ := by
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        exact (compl_compl X).symm
      rw [he]
      exact hp _
  | nu p hp =>
      show ((p.dual.denote M).comp (insert (fun i => (ρ i)ᶜ))).lfp =
        (((p.denote M).comp (insert ρ)).gfp)ᶜ
      apply lfp_complement_gfp
      intro X
      change p.dual.denote M (extend (fun i => (ρ i)ᶜ) X) =
        (p.denote M (extend ρ Xᶜ))ᶜ
      have he : extend (fun i => (ρ i)ᶜ) X = fun i => (extend ρ Xᶜ i)ᶜ := by
        funext i
        refine Fin.cases ?_ (fun _ => rfl) i
        exact (compl_compl X).symm
      rw [he]
      exact hp _

end Silmaril.Logic.ModalMu
