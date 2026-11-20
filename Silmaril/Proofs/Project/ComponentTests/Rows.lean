module

public import Silmaril.Project.Shapes.ComponentTest.Defs
public import Silmaril.Wasm.Component.InstTests.Thms

/-!
# Component test rows: proofs

The rows of `Silmaril.Project.ComponentTests`, from the theorems about the two binaries
(`Silmaril.Wasm.Component.InstTests.Thms`).
-/

@[expose] public section

namespace Silmaril.Proofs.Project.ComponentTests

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component
open Silmaril.Wasm.Component.InstTests
open Silmaril.Project.Shapes.ComponentTest

theorem trace_starts : TraceOf unitHost startsTrace := by
  intro x hx
  simp only [startsTrace, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> rfl

theorem starts_instantiates : Instantiates startsBytes unitHost startsTrace :=
  ⟨startsComp, parse_starts, trace_starts,
    fun P => (startsComp.denI _).of_prefix (starts_inst P) (List.prefix_append _ _),
    fun o => ⟨fun _ hp => starts_asks o hp, fun _ _ hp hh => starts_complete o hp hh⟩⟩

theorem starts_get_after_inst :
    ExportReturnsAfterInst startsBytes unitHost startsTrace getV v42 :=
  ⟨startsComp, parse_starts, trace_starts, starts_inst,
    fun o _ hp _ _ hr => starts_get o hp hr⟩

theorem trap_inst_traps : InstTraps trapBytes unitHost [] := by
  refine ⟨trapComp, parse_trap, (fun _ h => nomatch h), trap_inst, fun o p hp => ⟨?_, fun _ =>
    ⟨trap_not_ready o hp, trap_no_exports o hp⟩⟩⟩
  rw [trap_no_host_calls o hp]
  exact List.prefix_refl _

end Silmaril.Proofs.Project.ComponentTests
