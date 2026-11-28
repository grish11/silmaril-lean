module

public import Silmaril.Machine.MulticoreVM.Synchronized.Legacy.Defs
public import Silmaril.Machine.MulticoreVM.Placed.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Synchronized

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Synchronized
open Silmaril.Machine.MulticoreVM.Synchronized.Legacy

private theorem config_threads (words : Shared) (cfg : Toy.Config) (thread : ThreadId) :
    (config words cfg).threads thread = (cfg thread).map (fun core => .runnable (localState core)) :=
  rfl

private theorem config_put (words : Shared) (cfg : Toy.Config) (thread : ThreadId)
    (core : Toy.Core) :
    config words (Toy.put cfg thread core) =
      (config words cfg).put thread (.runnable (localState core)) := by
  unfold config Toy.put ThreadSync.Config.put
  congr
  funext t
  split <;> rfl

theorem exec_embed (words : Shared) (cfg : Toy.Config) (thread : ThreadId)
    (child : Option ThreadId) :
    Synchronized.exec thread (choice child) (config words cfg) =
      (Toy.exec thread child cfg).map (fun (next, fragment) =>
        (config words next, fragment.map localLetter)) := by
  cases atThread : cfg thread with
  | none =>
    cases child <;> simp [Synchronized.exec, ThreadSync.exec, choice, config_threads, Toy.exec, atThread]
  | some core =>
    rcases core with ⟨reg, code⟩
    cases code with
    | nil =>
      cases child <;>
        simp [Synchronized.exec, ThreadSync.exec, program, choice, config_threads,
          Toy.exec, localState, instructions, atThread]
    | cons head tail =>
      cases child with
      | none =>
        cases head <;>
          simp [Synchronized.exec, ThreadSync.exec, program, choice, config_put, config_threads, Toy.exec,
            localState, instr, instructions, localLetter, atThread]
      | some child =>
        cases head with
        | add _ | emit =>
          simp [Synchronized.exec, choice, config_threads, Toy.exec, localState, instr, instructions, atThread]
        | spawn _ _ =>
          cases atChild : cfg child <;>
            simp [Synchronized.exec, choice, config_put, config_threads, Toy.exec, localState, instr,
              instructions, localLetter, atThread, atChild]

private theorem name_map (thread : ThreadId) (fragment : Fragment ThreadId Nat) :
    nameFragment thread (fragment.map localLetter) = (nameFragment thread fragment).map letter := by
  simp only [nameFragment, List.map_map]
  exact List.map_congr_left fun l _ => by cases l <;> rfl

theorem execute_embed (words : Shared) (cfg : Toy.Config)
    (old : Schedule ThreadId (Option ThreadId)) :
    execute Synchronized.exec (schedule old) (config words cfg) =
      (execute Toy.exec old cfg).map (fun (next, word) => (config words next, word.map letter)) := by
  induction old generalizing cfg with
  | nil => rfl
  | cons decision rest ih =>
    simp only [schedule, List.map_cons, execute, exec_embed]
    cases step : Toy.exec decision.thread decision.choice cfg with
    | none => rfl
    | some result =>
      rcases result with ⟨next, fragment⟩
      change
        (do
          let (final, tail) ← execute Synchronized.exec (schedule rest) (config words next)
          pure (final, nameFragment decision.thread (fragment.map localLetter) ++ tail)) = _
      rw [ih]
      cases tailRun : execute Toy.exec rest next with
      | none => simp [tailRun]
      | some outcome =>
        rcases outcome with ⟨final, tail⟩
        simp [tailRun, List.map_append, name_map]

theorem placed_refines {CoreId Core : Type} [DecidableEq CoreId]
    {actions : Placed.Schedule CoreId ThreadId (Option ThreadId)}
    {initial final : Placed.Config CoreId ThreadId Core Toy.Core}
    {word : Placed.TaggedWord CoreId ThreadId Nat} (words : Shared)
    (run : Placed.Scheduled (Placed.ofThreadStep Toy.step) actions initial word final) :
    Scheduled Synchronized.step (schedule (Placed.threadSchedule actions)) (config words initial.threads)
      ((Placed.threadWord word).map letter) (config words final.threads) := by
  have projected := run.refines (Placed.ofThreadStep_refines Toy.step)
  apply (execute_iff_scheduled Synchronized.exec _).mp
  rw [execute_embed, (execute_iff_scheduled Toy.exec _).mpr projected]
  rfl

end Silmaril.Proofs.Machine.MulticoreVM.Synchronized
