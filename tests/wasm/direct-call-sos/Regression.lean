module

import Silmaril.Wasm.Institution.Operational.CallResolution.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Institution.Operational.CallResolution
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private def i : FuncIdx := ⟨0⟩
private def a : Runtime.FuncAddr := ⟨0⟩
private def f : Runtime.Frame := ⟨[], { funcs := [a] }⟩
private def s : V1.Execution.Store Unit := { funcs := [.host ⟨[], []⟩ ()] }
private abbrev t : Lime1.Execution.Store Unit := s.mapCode V1.Func.toLime
private def host : V1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def limeHost : Lime1.Execution.HostSemantics Unit := fun _ _ _ _ => False

private theorem edge : Edge f.module.funcs (.call i) (.invoke a) := resolves rfl

private theorem allocatedTarget : Allocated t f i := by
  intro b lookup
  have eq : some a = some b := lookup
  cases eq
  rfl

example : V1.Execution.Step host (v1Config s f (.call i)) (v1Config s f (.invoke a)) :=
  v1_step_iff.mpr ⟨a, edge, rfl⟩

example : Lime1.Execution.Step limeHost (v1Config s f (.call i)).toLime (v1Config s f (.invoke a)).toLime := by
  rw [v1_to_lime, v1_to_lime]
  exact lime_step_iff.mpr ⟨a, edge, rfl⟩

example : Core.Step Numerics.Profile.spec noHost (v1Config s f (.call i)).toLime.toCore
    (v1Config s f (.invoke a)).toLime.toCore := by
  rw [v1_to_lime, v1_to_lime]
  exact core_sound allocatedTarget edge

example {target : Core.Config Unit}
    (step : Core.Step Numerics.Profile.spec noHost (v1Config s f (.call i)).toLime.toCore target) :
    ∃ out, Edge f.module.funcs (.call i) (.invoke out) ∧
      target = (v1Config s f (.invoke out)).toLime.toCore := by
  rw [v1_to_lime] at step
  obtain ⟨out, resolved, _, eq⟩ := core_readback step
  exact ⟨out, resolved, by rw [v1_to_lime, eq]⟩

-- A dangling runtime address still resolves in V1, but Core needs the function type.
example : V1.Execution.Step host (v1Config {} f (.call i)) (v1Config {} f (.invoke a)) :=
  v1_step_iff.mpr ⟨a, edge, rfl⟩

example {target : Core.Config Unit} :
    ¬ Core.Step Numerics.Profile.spec noHost
      (limeConfig ({} : Lime1.Execution.Store Unit) f (.call i)).toCore target := by
  intro step
  obtain ⟨_, _, allocated, _⟩ := core_readback step
  contradiction
