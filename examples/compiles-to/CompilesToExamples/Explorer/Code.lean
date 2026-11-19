module

public import CompilesToExamples.Straight.Rows
public import CompilesToExamples.Branch.Rows

/-!
# The examples' code is the registered objects' code

Per build, the function's bytes (`FnData.code`, the bytes every statement of
`CompilesToExamples.Explorer.Builds` is about) are the code of its symbol in the object file
registered in `silmaril/artifacts.toml` (the value `silmaril.compiles_to.<file>.<build>.obj` reads
it; the kernel decodes the ELF: `elf.object_fn`). This ties the Lean function of a compiler
explorer problem to its target artifact. Restated from the generated rows.
-/

@[expose] public section

namespace CompilesToExamples.Explorer

open Silmaril.Project.Shapes.SysV (ObjectFn)

theorem straight_O0_code :
    ObjectFn silmaril.compiles_to.straight.o0.obj "add3" CompilesToExamples.Straight.O0.add3.code :=
  CompilesToExamples.Straight.Rows.o0_add3_code

theorem straight_O2_code :
    ObjectFn silmaril.compiles_to.straight.o2.obj "add3" CompilesToExamples.Straight.O2.add3.code :=
  CompilesToExamples.Straight.Rows.o2_add3_code

theorem branch_O0_code :
    ObjectFn silmaril.compiles_to.branch.o0.obj "max2" CompilesToExamples.Branch.O0.max2.code :=
  CompilesToExamples.Branch.Rows.o0_max2_code

theorem branch_O2_code :
    ObjectFn silmaril.compiles_to.branch.o2.obj "max2" CompilesToExamples.Branch.O2.max2.code :=
  CompilesToExamples.Branch.Rows.o2_max2_code

end CompilesToExamples.Explorer

end
