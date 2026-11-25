module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Core.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.LegacyDivision.CoreReadback

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Runtime (AdminInstr)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {I H : Type} {S : Syntax I}

/-- Every native Core successor of emitted admitted code reads back to a
derivable legacy edge, with exact re-emission and an unchanged Core world. -/
theorem CoreEncoding.step_readback (E : CoreEncoding S) (P : Profile) (s : Store H) (f : Frame)
    {before : List (AdminInstr I)} {target : Config H} (ok : Admitted S before)
    (step : Step P noHost ⟨s, f, emitCode E.emit before⟩ target) :
    ∃ after, DerivesEdge S before after ∧ target = ⟨s, f, emitCode E.emit after⟩ :=
  Proofs.step_readback E P s f ok step

theorem CoreEncoding.steps_to_core (E : CoreEncoding S) (P : Profile) (s : Store H) (f : Frame)
    {before after : List (AdminInstr I)} (h : DerivesPath S before after) :
    Steps P noHost ⟨s, f, emitCode E.emit before⟩ ⟨s, f, emitCode E.emit after⟩ :=
  Relation.ReflTransGen.lift (p := Step P noHost) (fun code => (⟨s, f, emitCode E.emit code⟩ : Config H))
    (fun _ _ edge => E.step_to_core P s f edge) _ _ h

theorem CoreEncoding.steps_readback (E : CoreEncoding S) (P : Profile) (s : Store H) (f : Frame)
    {before : List (AdminInstr I)} {target : Config H} (ok : Admitted S before)
    (path : Steps P noHost ⟨s, f, emitCode E.emit before⟩ target) :
    ∃ after, DerivesPath S before after ∧ target = ⟨s, f, emitCode E.emit after⟩ :=
  Proofs.steps_readback E P s f ok path

end Silmaril.Wasm.Institution.Operational.LegacyDivision
