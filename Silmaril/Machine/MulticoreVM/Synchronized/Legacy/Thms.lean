module

public import Silmaril.Machine.MulticoreVM.Synchronized.Legacy.Defs
public import Silmaril.Machine.MulticoreVM.Placed.Thms
import Silmaril.Proofs.Machine.MulticoreVM.Synchronized.Legacy

public section

namespace Silmaril.Machine.MulticoreVM.Synchronized.Legacy

/-- The embedding preserves the result of one old instruction, including rejections. -/
theorem exec_embed (words : Shared) (cfg : Toy.Config) (thread : ThreadId)
    (child : Option ThreadId) :
    Synchronized.exec thread (choice child) (config words cfg) =
      (Toy.exec thread child cfg).map (fun (next, fragment) =>
        (config words next, fragment.map localLetter)) :=
  Proofs.Machine.MulticoreVM.Synchronized.exec_embed words cfg thread child

/-- Exact finite compatibility for old programs and choices, including failures, spawn
participants, and unchanged shared words. -/
theorem execute_embed (words : Shared) (cfg : Toy.Config)
    (old : Schedule ThreadId (Option ThreadId)) :
    execute Synchronized.exec (schedule old) (config words cfg) =
      (execute Toy.exec old cfg).map (fun (next, word) => (config words next, word.map letter)) :=
  Proofs.Machine.MulticoreVM.Synchronized.execute_embed words cfg old

/-- An old C8 run erases placement by the original theorem before embedding the legacy fragment. -/
theorem placed_refines {CoreId Core : Type} [DecidableEq CoreId]
    {actions : Placed.Schedule CoreId ThreadId (Option ThreadId)}
    {initial final : Placed.Config CoreId ThreadId Core Toy.Core}
    {word : Placed.TaggedWord CoreId ThreadId Nat} (words : Shared)
    (run : Placed.Scheduled (Placed.ofThreadStep Toy.step) actions initial word final) :
    Scheduled Synchronized.step (schedule (Placed.threadSchedule actions)) (config words initial.threads)
      ((Placed.threadWord word).map letter) (config words final.threads) :=
  Proofs.Machine.MulticoreVM.Synchronized.placed_refines words run

end Silmaril.Machine.MulticoreVM.Synchronized.Legacy
