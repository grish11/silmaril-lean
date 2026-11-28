module

public import Silmaril.Machine.MulticoreVM.Swaps.Defs

public section

namespace Silmaril.Proofs.Machine.MulticoreVM

open Silmaril.Machine.MulticoreVM
open Silmaril.Semantics.ConcurrentTrace (Word ofWord ofWord_append)

universe u

variable {State Thread Choice Event : Type u}
variable {step : Transition State Thread Choice Event} {initial : State}
variable {a b : Decision Thread Choice} {pre post source target : Schedule Thread Choice}
variable {allowed : Decision Thread Choice → Decision Thread Choice → Prop}

theorem scheduleReplay_pair_iff :
    ScheduleReplay step initial [a, b] [b, a] ↔
      ∀ ⦃middle final first second⦄,
        step a.thread a.choice initial first middle →
        step b.thread b.choice middle second final →
        ∃ middle' first' second',
          step b.thread b.choice initial first' middle' ∧
          step a.thread a.choice middle' second' final ∧
          ofWord (nameFragment a.thread first) * ofWord (nameFragment b.thread second) =
            ofWord (nameFragment b.thread first') * ofWord (nameFragment a.thread second') := by
  constructor
  · intro replay middle final first second takeA takeB
    obtain ⟨_, run, trace⟩ := replay (.cons takeA (.cons takeB (.nil final)))
    cases run with
    | cons takeB' rest =>
      cases rest with
      | cons takeA' done =>
        cases done
        exact ⟨_, _, _, takeB', takeA', by simpa only [List.append_nil, ofWord_append] using trace⟩
  · intro replay word final run
    cases run with
    | cons takeA rest =>
      cases rest with
      | cons takeB done =>
        cases done
        obtain ⟨_, _, _, takeB', takeA', trace⟩ := replay takeA takeB
        exact ⟨_, .cons takeB' (.cons takeA' (.nil _)), by
          simpa only [List.append_nil, ofWord_append] using trace⟩

private theorem scheduled_append_iff {final : State} {word : Word Thread Event} :
    Scheduled step (pre ++ post) initial word final ↔
      ∃ middle before after, Scheduled step pre initial before middle ∧
        Scheduled step post middle after final ∧ word = before ++ after := by
  induction pre generalizing initial word with
  | nil =>
    constructor
    · exact fun run => ⟨initial, [], word, .nil _, run, rfl⟩
    · rintro ⟨_, _, _, before, after, rfl⟩
      cases before
      exact after
  | cons decision pre ih =>
    constructor
    · intro run
      cases run with
      | cons first rest =>
        obtain ⟨middle, before, after, leftRun, rightRun, rfl⟩ := ih.mp rest
        exact ⟨middle, _, after, .cons first leftRun, rightRun, (List.append_assoc ..).symm⟩
    · rintro ⟨middle, _, after, leftRun, rightRun, rfl⟩
      cases leftRun with
      | cons first rest =>
        rw [List.append_assoc]
        exact .cons first (ih.mpr ⟨middle, _, after, rest, rightRun, rfl⟩)

private theorem replay_refl : ScheduleReplay step initial source source := by
  intro word final run
  exact ⟨word, run, rfl⟩

private theorem replay_trans {middle : Schedule Thread Choice}
    (first : ScheduleReplay step initial source middle)
    (second : ScheduleReplay step initial middle target) : ScheduleReplay step initial source target := by
  intro word final run
  obtain ⟨_, intermediate, trace₁⟩ := first run
  obtain ⟨_, replay, trace₂⟩ := second intermediate
  exact ⟨_, replay, trace₁.trans trace₂⟩

private theorem replay_append {pre' post' : Schedule Thread Choice}
    (first : ScheduleReplay step initial pre pre')
    (rest : ∀ ⦃middle word⦄, Scheduled step pre initial word middle →
      ScheduleReplay step middle post post') :
    ScheduleReplay step initial (pre ++ post) (pre' ++ post') := by
  intro word final run
  obtain ⟨middle, before, after, leftRun, rightRun, rfl⟩ := scheduled_append_iff.mp run
  obtain ⟨before', leftReplay, leftTrace⟩ := first leftRun
  obtain ⟨after', rightReplay, rightTrace⟩ := rest leftRun rightRun
  exact ⟨before' ++ after',
    scheduled_append_iff.mpr ⟨middle, before', after', leftReplay, rightReplay, rfl⟩, by
      rw [ofWord_append, ofWord_append, leftTrace, rightTrace]⟩

theorem adjacent_swap_replay
    (diamond : ∀ ⦃middle word⦄, Scheduled step pre initial word middle →
      LocalDiamond step middle a b) :
    ScheduleReplay step initial (pre ++ a :: b :: post) (pre ++ b :: a :: post) ∧
      ScheduleReplay step initial (pre ++ b :: a :: post) (pre ++ a :: b :: post) := by
  have inContext {left right : Schedule Thread Choice}
      (replay : ∀ ⦃middle word⦄, Scheduled step pre initial word middle →
        ScheduleReplay step middle left right) :
      ScheduleReplay step initial (pre ++ (left ++ post)) (pre ++ (right ++ post)) :=
    replay_append replay_refl fun ⦃_ _⦄ before =>
      replay_append (replay before) fun ⦃_ _⦄ _ => replay_refl
  exact ⟨inContext (fun ⦃_ _⦄ before => (diamond before).1),
    inContext (fun ⦃_ _⦄ before => (diamond before).2)⟩

theorem scheduleEquivalent_swap (h : allowed a b) :
    ScheduleEquivalent allowed (pre ++ a :: b :: post) (pre ++ b :: a :: post) := by
  let congruence := scheduleCongruence allowed
  have pair : congruence (.ofList [a, b]) (.ofList [b, a]) :=
    Con.le_conGen _ _ (.pair h)
  exact (congruence.refl (.ofList pre)).mul (pair.mul (congruence.refl (.ofList post)))

theorem scheduleEquivalent_replay (h : ScheduleEquivalent allowed source target)
    (sound : ∀ ⦃a b⦄, allowed a b → ∀ state, LocalDiamond step state a b)
    (initial : State) :
    ScheduleReplay step initial source target ∧ ScheduleReplay step initial target source := by
  have replay {x y : FreeMonoid (Decision Thread Choice)}
      (related : ConGen.Rel (DecisionSwap allowed) x y) (state : State) :
      ScheduleReplay step state x.toList y.toList ∧ ScheduleReplay step state y.toList x.toList := by
    induction related generalizing state with
    | of _ _ h =>
      cases h with
      | pair h => exact sound h state
    | refl => exact ⟨replay_refl, replay_refl⟩
    | symm _ ih => exact ⟨(ih state).2, (ih state).1⟩
    | trans _ _ first second =>
      exact ⟨replay_trans (first state).1 (second state).1,
        replay_trans (second state).2 (first state).2⟩
    | mul _ _ first second =>
      exact ⟨replay_append (first state).1 (fun ⦃middle _⦄ _ => (second middle).1),
        replay_append (first state).2 (fun ⦃middle _⦄ _ => (second middle).2)⟩
  exact replay h initial

theorem scheduleEquivalent_quotient_outcomes_eq (h : ScheduleEquivalent allowed source target)
    (sound : ∀ ⦃a b⦄, allowed a b → ∀ state, LocalDiamond step state a b)
    (initial : State) :
    observeQuotient '' scheduledOutcomes step source initial =
      observeQuotient '' scheduledOutcomes step target initial := by
  have image_subset {left right : Schedule Thread Choice}
      (replay : ScheduleReplay step initial left right) :
      observeQuotient '' scheduledOutcomes step left initial ⊆
        observeQuotient '' scheduledOutcomes step right initial := by
    rintro _ ⟨⟨final, word⟩, run, rfl⟩
    obtain ⟨swapped, path, trace⟩ := replay run
    exact ⟨(final, swapped), path, Prod.ext rfl trace.symm⟩
  obtain ⟨forward, backward⟩ := scheduleEquivalent_replay h sound initial
  exact Set.Subset.antisymm (image_subset forward) (image_subset backward)

end Silmaril.Proofs.Machine.MulticoreVM
