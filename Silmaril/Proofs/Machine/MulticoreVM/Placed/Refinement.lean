module

public import Mathlib.SetTheory.Cardinal.NatCard
public import Silmaril.Machine.MulticoreVM.Placed.Defs

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Placed

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Placed (Config TaggedWord threadWord coreWord tagFragment
  Action threadSchedule Instruction Scheduled)

universe u

variable {CoreId ThreadId Core Thread Choice Event : Type u}

theorem resident_card_le_present [Finite CoreId] (cfg : Config CoreId ThreadId Core Thread) :
    Nat.card cfg.Resident ≤ Nat.card cfg.PresentCore := by
  let core (t : cfg.Resident) : cfg.PresentCore :=
    ⟨t.property.choose, (cfg.endpoints t.property.choose_spec).1⟩
  apply Nat.card_le_card_of_injective core
  intro t u h
  have home : t.property.choose = u.property.choose := congrArg Subtype.val h
  apply Subtype.ext
  exact Option.some.inj (t.property.choose_spec.symm.trans (home ▸ u.property.choose_spec))

theorem threadWord_tagFragment (core : CoreId) (thread : ThreadId)
    (fragment : Fragment ThreadId Event) :
    threadWord (tagFragment core thread fragment) = nameFragment thread fragment := by
  simp only [threadWord, tagFragment, nameFragment, List.map_map]
  apply List.map_congr_left
  intro letter _
  cases letter <;> rfl

theorem coreWord_tagFragment (core : CoreId) (thread : ThreadId)
    (fragment : Fragment ThreadId Event) :
    coreWord (tagFragment core thread fragment) = fragment.map (fun
      | .event value => .event core (some value)
      | .sync _ => .event core none) := by
  simp only [coreWord, tagFragment, List.map_map]
  apply List.map_congr_left
  intro letter _
  cases letter <;> rfl

theorem scheduled_refines [DecidableEq CoreId]
    {instruction : Instruction CoreId ThreadId Core Thread Choice Event}
    {step : Transition (ThreadId → Option Thread) ThreadId Choice Event}
    (refines : instruction.Refines step)
    {schedule : List (Action CoreId ThreadId Choice)} {initial final : Config CoreId ThreadId Core Thread}
    {word : TaggedWord CoreId ThreadId Event} (run : Scheduled instruction schedule initial word final) :
    Silmaril.Machine.MulticoreVM.Scheduled step (threadSchedule schedule) initial.threads
      (threadWord word) final.threads := by
  induction run with
  | nil cfg => exact .nil cfg.threads
  | cons first _ ih =>
    cases first with
    | execute resident instructionStep =>
      rw [show threadWord (_ ++ _) = threadWord _ ++ threadWord _ from List.map_append,
        threadWord_tagFragment]
      exact .cons (refines resident instructionStep) ih
    | idle _ changes => exact changes.2.1.symm ▸ ih
    | assign _ _ _ changes => exact changes.2.1.symm ▸ ih
    | migrate _ _ _ changes => exact changes.2.1.symm ▸ ih

end Silmaril.Proofs.Machine.MulticoreVM.Placed
