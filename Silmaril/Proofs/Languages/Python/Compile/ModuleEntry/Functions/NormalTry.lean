module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NormalTry.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.NormalTry

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NormalTry

open Core.Module (ListHeap)
open Core.Module.Functions (Session)
open Core.Module.SeededCall (Namespace)
open Core.Closure.Executor (CodeTable)

theorem ordinary_writes {scope : Source.Scope} (table : CodeTable) (session : Session) (fuel : Nat)
    (writes : List (Write scope)) (rest : List (Run.Instruction scope)) :
    Run.runPrefix table (fuel + writes.length)
      (.ready session (writes.map (fun write => .scalar write.action) ++ rest)) =
      Run.runPrefix table fuel (.ready (writes.foldl
        (fun state write => state.bindGlobal write.name (Run.embed write.value)) session) rest) := by
  induction writes generalizing session with
  | nil => simp
  | cons write writes tail =>
    simpa only [List.length_cons, Nat.add_succ, List.map_cons, List.cons_append, Run.runPrefix, Write.action,
      Run.advance_scalarResultAssign, List.nil_append, List.foldl_cons] using
      tail (session.bindGlobal write.name (Run.embed write.value))

theorem seeded_writes {scope : Source.Scope} (space : Namespace) (context : Run.Seeded.CallContext)
    (writes : List (Write scope)) (rest : List (Run.Instruction scope)) (lists : ListHeap) :
    Run.Seeded.runInstructionsIn space context (writes.map (fun write => .scalar write.action) ++ rest) lists =
      Run.Seeded.runInstructionsIn (writes.foldl (fun state write =>
        state.bindGlobal write.name (Run.Seeded.seededValue (Run.embed write.value))) space) context rest lists := by
  induction writes generalizing space with
  | nil => rfl
  | cons write writes tail =>
    simpa only [List.map_cons, List.cons_append, Write.action, Run.Seeded.run_scalarResultAssign, List.foldl_cons] using
      tail (space.bindGlobal write.name (Run.Seeded.seededValue (Run.embed write.value)))

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.NormalTry
