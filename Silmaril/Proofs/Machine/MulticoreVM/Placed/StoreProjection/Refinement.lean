module

public import Silmaril.Machine.MulticoreVM.Placed.StoreProjection.Defs
public import Silmaril.Machine.MulticoreVM.Placed.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Placed.StoreProjection

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Placed (Config TaggedWord threadWord threadWord_append
  threadWord_tagFragment Action threadSchedule Instruction Scheduled StoreView)

universe u

variable {CoreId ThreadId Core Thread Choice Event State : Type u}

theorem scheduled_refinesBy [DecidableEq CoreId]
    {instruction : Instruction CoreId ThreadId Core Thread Choice Event}
    {view : StoreView CoreId ThreadId Core Thread State} {step : Transition State ThreadId Choice Event}
    (refines : instruction.RefinesBy view step)
    {schedule : List (Action CoreId ThreadId Choice)} {initial final : Config CoreId ThreadId Core Thread}
    {word : TaggedWord CoreId ThreadId Event} (run : Scheduled instruction schedule initial word final) :
    Silmaril.Machine.MulticoreVM.Scheduled step (threadSchedule schedule) (view initial.cores initial.threads)
      (threadWord word) (view final.cores final.threads) := by
  induction run with
  | nil cfg => exact .nil (view cfg.cores cfg.threads)
  | cons first _ ih =>
    cases first with
    | execute resident instructionStep =>
      rw [threadWord_append, threadWord_tagFragment]
      exact .cons (refines resident instructionStep) ih
    | idle _ changes | assign _ _ _ changes | migrate _ _ _ changes =>
      exact changes.1.symm ▸ changes.2.1.symm ▸ ih

end Silmaril.Proofs.Machine.MulticoreVM.Placed.StoreProjection
