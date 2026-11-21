module

public import Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped
import Silmaril.Wasm.Execution.Core.Entry.Determinism.Thms
import Silmaril.Wasm.Execution.Core.Entry.Thms
import Silmaril.Wasm.Behaviour.Refinement.Interpreter
import Silmaril.Wasm.Cfg.ProfileFree.Thms

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Entry.ClosedFunctional

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Entry
  Silmaril.Wasm.Execution.Core.Entry.ClosedFunctional Silmaril.Wasm.Numerics Silmaril.Wasm.Cfg.ProfileFree
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec
  Silmaril.Wasm.SingleThreaded.Exec.BehaviourRefinement Silmaril.Semantics.Operational
open Silmaril.Wasm.Profiles (GCMode)
open Silmaril.Wasm.Profiles.FunctionalISA (Atom Raw)
open Silmaril.Wasm.Validation (CValType)

private theorem atom_free {mode : GCMode} (atom : Atom mode) : IFree atom.erase := by
  cases atom <;> exact .atom id id

theorem raw_free {mode : GCMode} (raw : Raw mode) : ∀ instr ∈ raw.erase, IFree instr := by
  induction raw with
  | done => simp [Raw.erase]
  | cons head tail rest =>
    intro instr member
    rcases List.mem_cons.mp member with rfl | member
    · exact atom_free head
    · exact rest instr member
  | blockI32 body tail bodyFree rest =>
    intro instr member
    rcases List.mem_cons.mp member with rfl | member
    · exact .block _ bodyFree
    · exact rest instr member

variable {H : Type} {P Q : Profile} {s : Store H} {address : Nat} {args : List Val}
  {types : List CValType} {final : Config H} {result : Result}

theorem invoke_free (closed : Bodies s) : ConfigFree (invoke s address args) := by
  apply configFree_invoke
  intro entry member fn code
  obtain ⟨bodyFn, raw, bodyCode, erased⟩ := closed entry member
  cases FuncCode.wasm.inj (code.symm.trans bodyCode)
  rw [erased]
  exact raw_free raw

theorem finishes_unique (closed : Bodies s) {other : Config H} {second : Result}
    (left : Finishes P noHost (invoke s address args) final result)
    (right : Finishes Q noHost (invoke s address args) other second) : final = other ∧ result = second := by
  have free := invoke_free (address := address) (args := args) closed
  have firstRun : Finishes (profile neverFail) noHost (invoke s address args) final result :=
    ⟨profileFree_steps free left.1, left.2⟩
  have secondRun : Finishes (profile neverFail) noHost (invoke s address args) other second :=
    ⟨profileFree_steps free right.1, right.2⟩
  exact Entry.finishes_unique firstRun secondRun

theorem finishes_iff_run (closed : Bodies s) (typed : ConfigOk (invoke s address args) types) :
    Finishes P noHost (invoke s address args) final result ↔ final.code = result.toAdmin ∧
      ∃ fuel, runI neverFail fuel (invoke s address args) = (final, true) := by
  have free := invoke_free (address := address) (args := args) closed
  constructor
  · intro finished
    exact ⟨finished.2, runI_complete_typed typed (profileFree_steps free finished.1)
      (fun _ => not_step_of_terminal ⟨result, finished.2⟩)⟩
  · rintro ⟨code, fuel, ran⟩
    have steps := runI_steps_typed (o := neverFail) fuel typed
    rw [ran] at steps
    exact ⟨profileFree_steps free steps, code⟩

theorem export_may_iff_run (input : ExportInput H)
    (lookup : Game.Accept.exportFunc? input.ready.instance_ input.name = some address)
    (closed : Bodies input.ready.store) (typed : ConfigOk (invoke input.ready.store address input.args) types)
    (outcome : Outcome Intrinsic.Completion) : (rawExport P noHost types).May input outcome ↔
      ∃ final result fuel, runI neverFail fuel (invoke input.ready.store address input.args) = (final, true) ∧
        final.code = result.toAdmin ∧ Intrinsic.observeResult result = outcome := by
  have same := (policy_safe_and_may (P := P) (host := noHost) (fun {_ _} => noHost_preserves) typed).2 outcome
  constructor
  · rintro ⟨source, ⟨found, selected, rfl⟩, may⟩
    cases Option.some.inj (lookup.symm.trans selected)
    obtain ⟨final, result, finished, obs⟩ := ordinary_may.mp (same.mp may)
    obtain ⟨code, fuel, ran⟩ := (finishes_iff_run closed typed).mp finished
    exact ⟨final, result, fuel, ran, code, obs⟩
  · rintro ⟨final, result, fuel, ran, code, obs⟩
    exact ⟨_, ⟨address, lookup, rfl⟩, same.mpr (ordinary_may.mpr
      ⟨final, result, (finishes_iff_run closed typed).mpr ⟨code, fuel, ran⟩, obs⟩)⟩

end Silmaril.Proofs.Wasm.Execution.Core.Entry.ClosedFunctional
