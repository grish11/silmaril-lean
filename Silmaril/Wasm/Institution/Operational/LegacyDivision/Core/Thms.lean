module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Core.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.LegacyDivision.Core

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Execution.Runtime (AdminInstr)

variable {I H : Type} {S : Syntax I}

theorem CoreEncoding.code_roundtrip (E : CoreEncoding S) {code : List (AdminInstr I)}
    (h : Admitted S code) : readCode E.read (emitCode E.emit code) = some code :=
  Proofs.code_roundtrip E h

/-- Code-only transport at a fixed Core store and frame. -/
theorem CoreEncoding.step_to_core (E : CoreEncoding S) (P : Profile) (s : Store H) (f : Frame)
    {before after : List (AdminInstr I)} (h : DerivesEdge S before after) :
    Step P noHost ⟨s, f, emitCode E.emit before⟩ ⟨s, f, emitCode E.emit after⟩ :=
  Proofs.step_to_core E s f h

end Silmaril.Wasm.Institution.Operational.LegacyDivision
