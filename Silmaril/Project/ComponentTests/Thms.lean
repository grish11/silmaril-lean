module

public import Silmaril.Project.ComponentTests.Defs
public import Silmaril.Project.Shapes.ComponentTest.Thms
import Silmaril.Proofs.Project.ComponentTests.Rows

/-! # Component test rows: answers

All three rows are proved (`Silmaril.Proofs.Project.ComponentTests`), from the theorems of
`Silmaril.Wasm.Component.InstTests.Thms`: the bytes are lowered by the kernel's definitional
check, the start runs are Core 3.0 runs built from `Step` rules, the instances are computed by
`decide +kernel`, and the exclusions come from scripts bounding the modules at deterministic
profiles.
-/

public section

namespace Silmaril.Project.ComponentTests

/-- **`starts.wasm` instantiates with the trace `f(1)`, `f(2)`.** -/
@[solves "silmaril.component_tests.starts.instantiates"]
theorem starts_instantiates : silmaril.component_tests.starts.instantiates :=
  Silmaril.Proofs.Project.ComponentTests.starts_instantiates

/-- **`starts.wasm`: `get()` returns `42` after instantiation.** -/
@[solves "silmaril.component_tests.starts.get_after_inst"]
theorem starts_get_after_inst : silmaril.component_tests.starts.get_after_inst :=
  Silmaril.Proofs.Project.ComponentTests.starts_get_after_inst

/-- **`trap.wasm`: the instantiation traps as a whole.** -/
@[solves "silmaril.component_tests.trap.inst_traps"]
theorem trap_inst_traps : silmaril.component_tests.trap.inst_traps :=
  Silmaril.Proofs.Project.ComponentTests.trap_inst_traps

end Silmaril.Project.ComponentTests

silmaril group silmaril.component_tests
  (title := "Component tests: instantiation-time behaviour of component binaries")
  (children := [silmaril.shapes.component.test.instantiates,
    silmaril.shapes.component.test.inst_traps,
    silmaril.shapes.component.test.export_returns_after_inst,
    silmaril.component_tests.starts.instantiates, silmaril.component_tests.starts.get_after_inst,
    silmaril.component_tests.trap.inst_traps])
