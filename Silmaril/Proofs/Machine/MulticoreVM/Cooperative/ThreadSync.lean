module

public import Silmaril.Machine.MulticoreVM.Cooperative.Defs
public import Silmaril.Machine.MulticoreVM.ThreadSync.Defs

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Cooperative

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Cooperative

universe u

variable {Thread Key Value Local Output Choice Event : Type u}
variable [DecidableEq Thread] [DecidableEq Key] [DecidableEq Value]
variable {keyed : ThreadSync.Program Thread Key Value Local Output}
variable {cfg next : ThreadSync.Config Thread Key Value Local} {thread : Thread}
variable {program : Program (ThreadSync.Config Thread Key Value Local) Thread Choice Event}
variable {policy : DispatchPolicy (ThreadSync.Config Thread Key Value Local) Thread}

theorem threadSync_owned_yield_iff
    (live : ¬ program.finished thread cfg)
    (yieldStep : program.yieldTo thread cfg next ↔
      ThreadSync.step keyed thread [] cfg [.event .yield] next) :
    Step program policy thread .yield ⟨cfg, some thread⟩ [] ⟨next, none⟩ ↔
      ThreadSync.cooperativeStep keyed thread [] ⟨cfg, some thread⟩
        [.event .yield] ⟨next, none⟩ := by
  have same : Step program policy thread .yield ⟨cfg, some thread⟩ [] ⟨next, none⟩ ↔
      ThreadSync.exec keyed thread [] cfg = some (next, [.event .yield]) := by
    constructor
    · intro h
      cases h with
      | yield _ hy => exact yieldStep.mp hy
    · intro h
      exact .yield live (yieldStep.mpr h)
  rw [same]
  change _ ↔ ThreadSync.cooperativeExec keyed thread [] ⟨cfg, some thread⟩ =
    some (⟨next, none⟩, [.event .yield])
  cases result : ThreadSync.exec keyed thread [] cfg with
  | none => simp [ThreadSync.cooperativeExec, result]
  | some pair =>
    obtain ⟨vm, fragment⟩ := pair
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      simp [ThreadSync.cooperativeExec, result]
    · intro h
      simp [ThreadSync.cooperativeExec, result] at h
      exact ⟨h.1.1, h.2⟩

end Silmaril.Proofs.Machine.MulticoreVM.Cooperative
