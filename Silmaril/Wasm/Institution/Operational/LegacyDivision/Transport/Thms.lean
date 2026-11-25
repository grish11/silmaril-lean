module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.V1.Thms
public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Lime1.Thms
public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Core.Readback.Thms
public import Silmaril.Wasm.Lime1.Execution.Transport
import Silmaril.Proofs.Wasm.Institution.Operational.LegacyDivision.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision

variable {H : Type} {src : Silmaril.Wasm.V1.Execution.HostSemantics H}
  {dst : Silmaril.Wasm.Lime1.Execution.HostSemantics H}

theorem translated_supported {xs : List Silmaril.Wasm.V1.Execution.Admin} (h : V1.Supported xs) :
    Lime1.Supported (Silmaril.Wasm.V1.Execution.codeToLime xs) :=
  Proofs.translated_supported h

theorem translated_step {a b : Silmaril.Wasm.V1.Execution.Config H}
    (ready : V1.Supported a.code) (step : Silmaril.Wasm.V1.Execution.Step src a b) :
    Silmaril.Wasm.Lime1.Execution.Step dst a.toLime b.toLime :=
  Proofs.translated_step ready step

/-- Every native Lime1 successor of a translated admitted configuration lifts,
with exact target equality in the public configuration translation. -/
theorem translated_step_readback {a : Silmaril.Wasm.V1.Execution.Config H}
    {b : Silmaril.Wasm.Lime1.Execution.Config H}
    (ready : V1.Supported a.code) (step : Silmaril.Wasm.Lime1.Execution.Step dst a.toLime b) :
    ∃ c : Silmaril.Wasm.V1.Execution.Config H, Silmaril.Wasm.V1.Execution.Step src a c ∧ c.toLime = b :=
  Proofs.translated_step_readback ready step

theorem translated_steps {a b : Silmaril.Wasm.V1.Execution.Config H}
    (ready : V1.Supported a.code) (path : Silmaril.Wasm.V1.Execution.Steps src a b) :
    Silmaril.Wasm.Lime1.Execution.Steps dst a.toLime b.toLime :=
  Proofs.translated_steps ready path

theorem translated_steps_readback {a : Silmaril.Wasm.V1.Execution.Config H}
    {b : Silmaril.Wasm.Lime1.Execution.Config H}
    (ready : V1.Supported a.code) (path : Silmaril.Wasm.Lime1.Execution.Steps dst a.toLime b) :
    ∃ c : Silmaril.Wasm.V1.Execution.Config H, Silmaril.Wasm.V1.Execution.Steps src a c ∧ c.toLime = b :=
  Proofs.translated_steps_readback ready path

/-- Direct V1 emission and the route through Lime1 give the same flat Core code. -/
theorem emit_code_commutes (xs : List Silmaril.Wasm.V1.Execution.Admin) :
    emitCode Lime1.coreEncoding.emit (Silmaril.Wasm.V1.Execution.codeToLime xs) =
      emitCode V1.coreEncoding.emit xs :=
  Proofs.emit_code_commutes xs

end Silmaril.Wasm.Institution.Operational.LegacyDivision
