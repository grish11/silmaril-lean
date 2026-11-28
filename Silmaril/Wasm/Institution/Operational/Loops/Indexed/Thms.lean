module

public import Silmaril.Wasm.Institution.Operational.Loops.Indexed.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.Loops.IndexedHost

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Loops.LimeIndexedLoop

open Execution.Runtime (Frame Value)
open Wasm.Lime1.Execution

variable {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
  {loop : LimeIndexedLoop} {saved : List Value} {rest : List Admin} {dst : Config H}

/-- Exact entry splits the resolved parameter suffix off the active stack
and installs the parameter arity in the native loop label. -/
theorem entry_iff {args : List Value} (resolved : loop.Resolved f) (typed : loop.Parameters args) :
    Step host ⟨s, f, values (saved ++ args) ++ .source loop.instr :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ .label loop.signature.params.length [loop.instr]
        (values args ++ expression loop.body) :: rest⟩ :=
  Proofs.entry_iff resolved typed

/-- An unresolved index has no native loop-entry successor. -/
theorem bad_index {stack : List Value} (missing : f.module.types[loop.index.toNat]? = none) :
    ¬ Step host ⟨s, f, values stack ++ .source loop.instr :: rest⟩ dst :=
  Proofs.bad_index missing

/-- Depth-zero restart restores the pending loop with the parameter suffix.
The next entry uses the same lookup in the preserved active frame. -/
theorem restart_iff {scratch args : List Value} {skipped : List Admin}
    (resolved : loop.Resolved f) (typed : loop.Parameters args) :
    Step host ⟨s, f, values saved ++ .label loop.signature.params.length [loop.instr]
      (values (scratch ++ args) ++ .source (.br ⟨0⟩) :: skipped) :: rest⟩ dst ↔
      dst = ⟨s, f, values (saved ++ args) ++ .source loop.instr :: rest⟩ :=
  Proofs.restart_iff resolved typed

/-- Normal completion delivers the result signature above the saved prefix.
It discards the restart continuation and keeps the live store and frame. -/
theorem result_iff {payload : List Value} (resolved : loop.Resolved f) (typed : loop.Results payload) :
    Step host ⟨s, f, values saved ++ .label loop.signature.params.length [loop.instr] (values payload) :: rest⟩ dst ↔
      dst = ⟨s, f, values (saved ++ payload) ++ rest⟩ :=
  Proofs.result_iff resolved typed

end Silmaril.Wasm.Institution.Operational.Loops.LimeIndexedLoop
