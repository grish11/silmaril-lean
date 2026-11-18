module

public import Silmaril.Proofs.Sim.Core.Run

/-!
# Proofs: the lattice of partial-state simulators

Names are in `Silmaril.Sim.PRel` and `Silmaril.Sim.PSim`, exported by `Silmaril/Sim/Core/Thms.lean`.

* `PRel.Le` is a preorder (`Le.refl`, `Le.trans`); soundness is downward closed
  (`Sound.mono`); `bot` is the least element and sound; `havoc` is sound iff the reference
  always progresses;
* `sup`/`sSup` are least upper bounds and preserve soundness: the sound simulators form an
  ideal, whose greatest element is `best` (`best_sound`, `sound_iff_le_best`);
* `meet` is a greatest lower bound; `combine` (information join) is sound when the reference
  is deterministic (`Sound.combine`), and is above both components where both step;
* lifting: `Sound.frame` (along an inclusion of locations, the reference framing the rest),
  `Sound.lift` (along an injective map of locations), `Sound.liftCmd` (along a map of commands);
* machines: `Sound.simulation` (a sound partial-state simulator is a `Simulation`),
  `PSim.sound_iff`, `PSim.Sound.soundSome`, `PSim.Complete.coSimulation`.
-/

@[expose] public section

namespace Silmaril.Sim

variable {C C' L L' V O : Type}

namespace PRel

variable {s t u : PRel C L V} {B : Machine C L V}

/-- **Soundness decomposes per command** (per simulator method). -/
theorem sound_iff_forall_soundAt : s.Sound B ↔ ∀ c, s.SoundAt B c :=
  ⟨fun h c => h c, fun h c => h c⟩

theorem Le.refl (s : PRel C L V) : Le s s := fun _ _ p' h => ⟨p', h, PState.Le.refl _⟩

theorem Le.trans (h₁ : Le s t) (h₂ : Le t u) : Le s u := fun c p p' h => by
  obtain ⟨p₁, h₁', hle₁⟩ := h₁ c p p' h
  obtain ⟨p₂, h₂', hle₂⟩ := h₂ c p p₁ h₁'
  exact ⟨p₂, h₂', hle₁.trans hle₂⟩

/-- **Soundness is downward closed** in the refinement order. -/
theorem Sound.mono (hle : Le s t) (ht : t.Sound B) : s.Sound B := fun c p p' b hb hs => by
  obtain ⟨p'', ht', hle'⟩ := hle c p p' hs
  obtain ⟨b', hstep, hb'⟩ := ht c p p'' b hb ht'
  exact ⟨b', hstep, hle'.trans hb'⟩

theorem bot_le (s : PRel C L V) : Le bot s := fun _ _ _ h => h.elim

theorem bot_sound (B : Machine C L V) : (bot : PRel C L V).Sound B := fun _ _ _ _ _ h => h.elim

theorem havoc_sound_iff : (havoc : PRel C L V).Sound B ↔ ∀ c b, ∃ b', B.step c b b' := by
  constructor
  · intro h c b
    obtain ⟨b', hb, _⟩ := h c PState.bot PState.bot b (PState.bot_le _) rfl
    exact ⟨b', hb⟩
  · intro h c _ p' b _ hp'
    obtain ⟨b', hb⟩ := h c b
    exact ⟨b', hb, hp' ▸ PState.bot_le _⟩

theorem le_sup_left (s t : PRel C L V) : Le s (sup s t) := fun _ _ p' h =>
  ⟨p', .inl h, PState.Le.refl _⟩

theorem le_sup_right (s t : PRel C L V) : Le t (sup s t) := fun _ _ p' h =>
  ⟨p', .inr h, PState.Le.refl _⟩

theorem sup_le (h₁ : Le s u) (h₂ : Le t u) : Le (sup s t) u := fun c p p' h =>
  h.elim (h₁ c p p') (h₂ c p p')

theorem Sound.sup (hs : s.Sound B) (ht : t.Sound B) : (sup s t).Sound B :=
  fun c p p' b hb h => h.elim (hs c p p' b hb) (ht c p p' b hb)

theorem le_sSup {F : PRel C L V → Prop} (hs : F s) : Le s (sSup F) := fun _ _ p' h =>
  ⟨p', ⟨s, hs, h⟩, PState.Le.refl _⟩

theorem sSup_le {F : PRel C L V → Prop} (h : ∀ s, F s → Le s u) : Le (sSup F) u :=
  fun c p p' ⟨s, hs, h'⟩ => h s hs c p p' h'

theorem Sound.sSup {F : PRel C L V → Prop} (h : ∀ s, F s → s.Sound B) : (sSup F).Sound B :=
  fun c p p' b hb ⟨s, hs, h'⟩ => h s hs c p p' b hb h'

/-- The best simulator is sound. -/
theorem best_sound (B : Machine C L V) : (best B).Sound B := fun _ _ _ b hb h => h b hb

/-- **A simulator is sound iff it is below the best one.** -/
theorem sound_iff_le_best : s.Sound B ↔ Le s (best B) := by
  constructor
  · intro h c p p' hs
    exact ⟨p', fun b hb => h c p p' b hb hs, PState.Le.refl _⟩
  · intro h
    exact Sound.mono h (best_sound B)

theorem meet_le_left [DecidableEq V] (s t : PRel C L V) : Le (meet s t) s :=
  fun _ _ _ ⟨p₁, _, h₁, _, he⟩ => ⟨p₁, h₁, he ▸ PState.meet_le_left _ _⟩

theorem meet_le_right [DecidableEq V] (s t : PRel C L V) : Le (meet s t) t :=
  fun _ _ _ ⟨_, p₂, _, h₂, he⟩ => ⟨p₂, h₂, he ▸ PState.meet_le_right _ _⟩

/-- `meet` is a greatest lower bound. -/
theorem le_meet [DecidableEq V] (h₁ : Le u s) (h₂ : Le u t) : Le u (meet s t) :=
  fun c p p' h => by
    obtain ⟨p₁, hs, hle₁⟩ := h₁ c p p' h
    obtain ⟨p₂, ht, hle₂⟩ := h₂ c p p' h
    exact ⟨PState.meet p₁ p₂, ⟨p₁, p₂, hs, ht, rfl⟩, PState.le_meet hle₁ hle₂⟩

theorem Sound.meet_left [DecidableEq V] (hs : s.Sound B) (t : PRel C L V) :
    (meet s t).Sound B := Sound.mono (meet_le_left s t) hs

/-- **Combining two sound simulators** (information join of their results) is sound for a
deterministic reference. -/
theorem Sound.combine (hdet : B.Deterministic) (hs : s.Sound B) (ht : t.Sound B) :
    (combine s t).Sound B := fun c p p' b hb ⟨p₁, p₂, h₁, h₂, he⟩ => by
  obtain ⟨b₁, hb₁, hle₁⟩ := hs c p p₁ b hb h₁
  obtain ⟨b₂, hb₂, hle₂⟩ := ht c p p₂ b hb h₂
  cases hdet c b b₁ b₂ hb₁ hb₂
  exact ⟨b₁, hb₁, he ▸ PState.join_le hle₁ hle₂⟩

/-- Where both step compatibly, `combine` is above each component. -/
theorem le_combine_left (c : C) (p p₁ p₂ : PState L V) (h₁ : s c p p₁) (h₂ : t c p p₂) :
    ∃ p'', combine s t c p p'' ∧ p₁ ⊑ p'' :=
  ⟨_, ⟨p₁, p₂, h₁, h₂, rfl⟩, PState.le_join_left _ _⟩

/-- **Frame**: a simulator sound for the reference stays sound when it copies the locations
outside `K` and the reference keeps them. -/
theorem Sound.frame {K : L → Prop} (hs : s.Sound B) (hK : ∀ c, B.Frames c K) :
    (frame K s).Sound B := fun c p p' b hb ⟨q, hq, he⟩ => by
  obtain ⟨b', hstep, hle⟩ := hs c p q b hb hq
  refine ⟨b', hstep, he ▸ PState.override_le hle fun l v hl hp => ?_⟩
  rw [hK c b b' hstep l hl]
  exact hb l v hp

/-- **Lift along an embedding of locations**: a simulator sound for the restricted reference
is sound for the whole one, if the reference keeps the locations outside the image. -/
theorem Sound.lift {e : L → L'} (he : Function.Injective e) {s : PRel C L V}
    {B : Machine C L' V} (hs : s.Sound (B.comapLoc e))
    (hK : ∀ c, B.Frames c fun l' => ∃ l, e l = l') : (lift e s).Sound B :=
  fun c p p' b hb ⟨q, hq, hp'⟩ => by
  obtain ⟨b', hstep, hle⟩ := hs c (PState.comap e p) q b (PState.comap_mono e hb) hq
  refine ⟨b', hstep, hp' ▸ fun l' v h => ?_⟩
  by_cases hl : ∃ l, e l = l'
  · obtain ⟨l, rfl⟩ := hl
    rw [PState.pushAlong_apply_of_injective he] at h
    exact hle l v h
  · rw [PState.pushAlong_apply_of_not q p hl] at h
    rw [hK c b b' hstep l' hl]
    exact hb l' v h

/-- **Lift along a map of commands.** -/
theorem Sound.liftCmd {f : C → C'} {s : PRel C L V} {B : Machine C' L V}
    (hs : s.Sound (B.comapCmd f)) : (liftCmd f s).Sound B :=
  fun _ p p' b hb ⟨c, hc, h⟩ => hc ▸ hs c p p' b hb h

/-- **A sound partial-state simulator is a `Simulation`** (relation: "is true of"). -/
def Sound.simulation (hs : s.Sound B) : Simulation s.toMachine B where
  R p b := p ⊑ B.view b
  view_le h := h
  step {c p p' b} h hst := hs c p p' b h hst
  load b := ⟨B.view b, PState.Le.refl _, rfl⟩

theorem Sound.sound (hs : s.Sound B) : Silmaril.Sim.Sound s.toMachine B := ⟨hs.simulation⟩

end PRel

namespace PSim

variable {S : PSim C L V O} {B : Machine C L V}

theorem sound_iff : S.Sound B ↔ S.rel.Sound B :=
  ⟨fun h c p p' b hb ⟨o, ho⟩ => h c o p p' b hb ho,
    fun h c o p p' b hb ho => h c p p' b hb ⟨o, ho⟩⟩

theorem Sound.soundSome (h : S.Sound B) : S.SoundSome B := fun c p b hb ⟨o, p', ho⟩ => by
  obtain ⟨b', hstep, hle⟩ := h c o p p' b hb ho
  exact ⟨o, p', b', ho, hstep, hle⟩

/-- **A complete oracle simulator is a `CoSimulation`**: every reference behaviour is the
simulator's for some oracle answer, so demonic properties transfer. -/
def Complete.coSimulation (h : S.Complete B) : CoSimulation S.toMachine B where
  R p b := p = B.view b
  view_eq h := h
  step {c p b b'} hp hst := by
    obtain ⟨o, ho⟩ := h c b b' hst
    exact ⟨B.view b', ⟨o, hp ▸ ho⟩, rfl⟩
  load b := ⟨B.view b, rfl⟩

/-- **An exactly sound oracle simulator is an exact simulation**: it may branch on values it
drew from the oracle, and transfers every angelic property (`Simulation.angelicExact`). -/
def SoundExact.simulation (h : S.SoundExact B) : Simulation S.toMachine B where
  R p b := p = B.view b
  view_le h := h ▸ PState.Le.refl _
  step {c p p' b} hp hst := by
    obtain ⟨o, ho⟩ := hst
    obtain ⟨b', hb', he⟩ := h c o b p' (hp ▸ ho)
    exact ⟨b', hb', he⟩
  load b := ⟨B.view b, rfl, rfl⟩

theorem SoundExact.exact (h : S.SoundExact B) : h.simulation.Exact := fun hR => hR

theorem SoundExact.exactSound (h : S.SoundExact B) : ExactSound S.toMachine B :=
  ⟨h.simulation, h.exact⟩

end PSim

end Silmaril.Sim

end
