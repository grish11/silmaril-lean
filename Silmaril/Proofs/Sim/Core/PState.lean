module

public import Silmaril.Sim.Core.Defs

/-!
# Proofs: the information order on partial states

Names are in `Silmaril.Sim.PState`, exported by the header `Silmaril/Sim/Core/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.PState

variable {L L' V : Type}

theorem Le.refl (p : PState L V) : p ⊑ p := fun _ _ h => h

theorem Le.trans {p q r : PState L V} (h₁ : p ⊑ q) (h₂ : q ⊑ r) : p ⊑ r :=
  fun l v h => h₂ l v (h₁ l v h)

theorem Le.antisymm {p q : PState L V} (h₁ : p ⊑ q) (h₂ : q ⊑ p) : p = q := by
  funext l
  cases hp : p l with
  | none =>
    cases hq : q l with
    | none => rfl
    | some v => rw [h₂ l v hq] at hp; cases hp
  | some v => rw [h₁ l v hp]

theorem bot_le (p : PState L V) : (bot : PState L V) ⊑ p := fun _ _ h => by cases h

theorem le_ofTotal_iff {p : PState L V} {s : L → V} :
    p ⊑ ofTotal s ↔ ∀ l v, p l = some v → v = s l := by
  constructor
  · intro h l v hv
    have := h l v hv
    simp only [ofTotal, Option.some.injEq] at this
    exact this.symm
  · intro h l v hv
    simp [ofTotal, h l v hv]

theorem comap_mono (e : L → L') {p q : PState L' V} (h : p ⊑ q) : comap e p ⊑ comap e q :=
  fun l v hv => h (e l) v hv

theorem comap_id (p : PState L V) : comap id p = p := rfl

theorem comap_comap {L'' : Type} (e : L → L') (e' : L' → L'') (p : PState L'' V) :
    comap e (comap e' p) = comap (fun l => e' (e l)) p := rfl

theorem le_join_left (p q : PState L V) : p ⊑ join p q := fun l v h => by
  simp [join, h]

theorem le_join_right {p q : PState L V} (h : Compat p q) : q ⊑ join p q := fun l v hq => by
  unfold join
  cases hp : p l with
  | none => simp [hq]
  | some w => simp [h l w v hp hq]

theorem join_le {p q r : PState L V} (hp : p ⊑ r) (hq : q ⊑ r) : join p q ⊑ r := fun l v h => by
  unfold join at h
  cases e : p l with
  | none => rw [e] at h; exact hq l v h
  | some w => rw [e] at h; cases h; exact hp l _ e

theorem compat_of_le {p q r : PState L V} (hp : p ⊑ r) (hq : q ⊑ r) : Compat p q :=
  fun l v w h₁ h₂ => by
    have := (hp l v h₁).symm.trans (hq l w h₂)
    cases this
    rfl

theorem meet_le_left [DecidableEq V] (p q : PState L V) : meet p q ⊑ p := fun l v h => by
  unfold meet at h
  split at h
  · exact h
  · cases h

theorem meet_le_right [DecidableEq V] (p q : PState L V) : meet p q ⊑ q := fun l v h => by
  unfold meet at h
  split at h
  · rename_i e; rw [← e]; exact h
  · cases h

theorem le_meet [DecidableEq V] {p q r : PState L V} (hp : r ⊑ p) (hq : r ⊑ q) :
    r ⊑ meet p q := fun l v h => by
  unfold meet
  rw [hp l v h, hq l v h]
  simp

theorem override_le {K : L → Prop} {q p x : PState L V} (hq : q ⊑ x)
    (hp : ∀ l v, ¬ K l → p l = some v → x l = some v) : override K q p ⊑ x := fun l v h => by
  classical
  unfold override at h
  by_cases hK : K l
  · simp only [hK, ite_true] at h
    exact hq l v h
  · simp only [hK, ite_false] at h
    exact hp l v hK h

theorem pushAlong_apply_of_injective {e : L → L'} (he : Function.Injective e)
    (q : PState L V) (p : PState L' V) (l : L) : pushAlong e q p (e l) = q l := by
  classical
  unfold pushAlong
  split
  · rename_i h
    rw [he (Classical.choose_spec h)]
  · rename_i h
    exact absurd ⟨l, rfl⟩ h

theorem pushAlong_apply_of_not {e : L → L'} (q : PState L V) (p : PState L' V) {l' : L'}
    (h : ¬ ∃ l, e l = l') : pushAlong e q p l' = p l' := by
  classical
  unfold pushAlong
  split
  · rename_i h'; exact absurd h' h
  · rfl

theorem comap_pushAlong {e : L → L'} (he : Function.Injective e) (q : PState L V)
    (p : PState L' V) : comap e (pushAlong e q p) = q := by
  funext l
  exact pushAlong_apply_of_injective he q p l

theorem Mono.comap (e : L → L') {P : PState L V → Prop} (h : Mono P) :
    Mono fun q : PState L' V => P (comap e q) :=
  fun _ _ hpq hp => h _ _ (comap_mono e hpq) hp

end Silmaril.Sim.PState

end
