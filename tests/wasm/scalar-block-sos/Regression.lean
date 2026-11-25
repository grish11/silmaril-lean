module

import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Institution.Operational.Blocks
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev old : Execution.Runtime.Value := .int .i32 2
private abbrev fresh : Execution.Runtime.Value := .int .i32 91
private abbrev slot : LocalIdx := ⟨0⟩
private abbrev result : Option NumType := some (.int .i32)
private abbrev body : Locals.State := ⟨[old], [.value fresh, .set slot, .get slot]⟩
private abbrev afterSet : Locals.State := ⟨[fresh], [.get slot]⟩
private abbrev afterGet : Locals.State := ⟨[fresh], [.value fresh]⟩
private abbrev start : State := .block result body
private abbrev final : State := .done [fresh] [fresh]
private abbrev m : Execution.Runtime.ModuleInst := { globals := [⟨0⟩] }
private abbrev s : V1.Execution.Store Unit := { globals := [⟨old, .var⟩] }
private def v1Host : V1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def limeHost : Lime1.Execution.HostSemantics Unit := fun _ _ _ _ => False

private theorem write : Locals.Edge body afterSet :=
  Locals.context (Locals.fact (.set [old] slot fresh (by decide))) [] [.get slot]

private theorem read : Locals.Edge afterSet afterGet :=
  Locals.fact (.get [fresh] slot fresh rfl)

private theorem path : Runs start final :=
  (((Relation.ReflTransGen.single (enter result body)).tail
    (reduce result write)).tail (reduce result read)).tail (exit result [fresh] [fresh])

private theorem typed : Admitted [.int .i32] result start := ⟨rfl, rfl, rfl⟩
private theorem finished : Admitted [.int .i32] result final := ⟨rfl, rfl⟩

example : V1.Execution.Steps v1Host (v1Config s m start) (v1Config s m final) :=
  (v1_run_iff typed).mpr ⟨final, path, finished, rfl⟩

example : Lime1.Execution.Steps limeHost (v1Config s m start).toLime (v1Config s m final).toLime := by
  rw [v1_to_lime, v1_to_lime]
  exact (lime_run_iff typed).mpr ⟨final, path, finished, rfl⟩

example : Execution.Core.Steps Numerics.Profile.spec noHost
    (v1Config s m start).toLime.toCore (v1Config s m final).toLime.toCore := by
  rw [v1_to_lime, v1_to_lime, lime_to_core, lime_to_core]
  exact (core_run_iff typed).mpr ⟨final, path, finished, rfl⟩

example {target : Execution.Core.Config Unit}
    (steps : Execution.Core.Steps Numerics.Profile.spec noHost (v1Config s m start).toLime.toCore target) :
    ∃ out, Runs start out ∧ Admitted [.int .i32] result out ∧
      target = (v1Config s m out).toLime.toCore := by
  rw [v1_to_lime, lime_to_core] at steps
  obtain ⟨out, path, types, eq⟩ := (core_run_iff typed).mp steps
  refine ⟨out, path, types, ?_⟩
  rw [v1_to_lime, lime_to_core, eq]

example : (v1Config s m final).toLime.toCore.frame.locals = [Locals.coreLocal fresh] ∧
    (v1Config s m final).toLime.toCore.store = (v1Config s m start).toLime.toCore.store :=
  ⟨rfl, rfl⟩

example : ¬ Admitted [] result (.block result ⟨[], []⟩) := by
  rintro ⟨_, _, checked⟩
  contradiction

example : Runs (.block none ⟨[], []⟩) (.done [] []) :=
  (Relation.ReflTransGen.single (enter none ⟨[], []⟩)).tail (exit none [] [])
