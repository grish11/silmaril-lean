module

public import Silmaril.Project.Registry.Institution.Defs
public import Silmaril.Wasi.Spec.Defs
public import Silmaril.Wasi.World.Defs

/-!
# Logic graph: the institutions and rooms of `Silmaril.Wasi`

Registrations of the institution and room declarations of the `Wasi` tree (`docs/projects/logic-graph.md`): Lean checks each declaration's type; a family is registered as a family.
-/

silmaril institution wasi.spec.inc_inst := Silmaril.Wasi.Spec.IncInst
silmaril institution wasi.spec.wasi_inst1 := Silmaril.Wasi.Spec.WasiInst₁
silmaril institution wasi.spec.wasi_inst := Silmaril.Wasi.Spec.wasiInst
silmaril institution wasi.wasi_inst := Silmaril.Wasi.WasiInst
