module

public import CompilesToExamples.Straight.Thms
public import CompilesToExamples.Branch.Thms
public import Silmaril.Project.Shapes.CompilesTo.Explorer.Thms

/-!
# The compiles-to examples as compilation problems

The `straight.c` and `branch.c` builds of `examples/compiles-to` (gcc 13.3.0, pinned by digest)
read through `Silmaril.Compiler.Explorer`: per build, each edge of the mapping, the whole
mapping, the translation (the generic, backward refinement), its non-vacuity, the ABI entry and
the refinement of the location relation, each its own theorem, so that `tools/compiler-explorer`
can check each one by its statement.

The theorems restate results of the generated proof modules (`CompilesToExamples.<File>.Proofs.*`)
and the generic theorems; none adds an assumption. `branch.c` at `-O2` (one point,
`cmp; mov; cmovge; ret`) has no proved segment: its edge, its mapping and its translation stay
open (`Task.max2_seg_0`). Its ABI entry, its non-vacuity and its location refinement are proved:
none of them depends on the segments.

What stays open for every build: safety of the C function from *every* Core entry
(`Task.<f>_safe`), which `c.compiles_to` needs; the refinement here quantifies over safe
entries, and `inhabited` shows one exists.
-/

@[expose] public section

namespace CompilesToExamples.Explorer

open Silmaril.Project.CompilesTo Silmaril.Compiler.Explorer
open Silmaril.Cerberus.Core.Dynamics (Frame)

/-- The x86-64 model of the rows. -/
abbrev isa : Model := Silmaril.X86.Open.isa

/-! ## `straight.c`, `-O0`, `add3` (5 points) -/

namespace StraightO0

/-- The function and its code. -/
abbrev F : FnData := CompilesToExamples.Straight.O0.add3
/-- Edge 0: the segment from point 0 is simulated. -/
theorem edge_0 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 0 :=
  F.edgeValid_of_segment (Straight.O0.add3_segments 0) k0
/-- Edge 1: the segment from point 1 is simulated. -/
theorem edge_1 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 1 :=
  F.edgeValid_of_segment (Straight.O0.add3_segments 1) k0
/-- Edge 2: the segment from point 2 is simulated. -/
theorem edge_2 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 2 :=
  F.edgeValid_of_segment (Straight.O0.add3_segments 2) k0
/-- Edge 3: the segment from point 3 is simulated. -/
theorem edge_3 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 3 :=
  F.edgeValid_of_segment (Straight.O0.add3_segments 3) k0
/-- Edge 4: the segment from point 4 is simulated. -/
theorem edge_4 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 4 :=
  F.edgeValid_of_segment (Straight.O0.add3_segments 4) k0
/-- The whole mapping: every segment, at every point number. -/
theorem mapping_valid (k0 : List Frame) : (F.mapping isa k0).Valid :=
  fun k => F.edgeValid_of_segment (Straight.O0.add3_segments k) k0

/-- The translation: the machine, stopped at its first return, refines the Core run from every
System V call with a safe Core run. -/
theorem translation (k0 : List Frame) : (F.compilation isa k0).toProblem.Refines :=
  F.compilation_refines_of_segments isa k0 (fun _ => rfl) rfl Straight.O0.add3_segments

/-- Non-vacuity at the canonical entries: `c.compiles_to.canonical_entry` (one entry per argument
tuple, safe for some tuple). -/
theorem canonical :
    Silmaril.Project.Shapes.CompilesTo.CompilesToCanonical isa F.placement F.frame F.cfn :=
  Straight.O0.add3_canonical
/-- The System V entry exists: the placement can be entered for every argument tuple. -/
theorem abi : Silmaril.Project.Shapes.SysV.Enterable isa F.placement F.sig F.frame :=
  Straight.O0.add3_enterable

/-- The problem is not vacuous: a safe canonical Core entry is related to a System V entry. -/
theorem inhabited : (F.compilation isa []).toProblem.Inhabited :=
  F.compilation_inhabited isa (by decide) abi (by decide) (by decide +kernel) (by decide)
    (by decide +kernel) Straight.add3Args Straight.add3_args_safe

/-- The mapping refines the location relation at every point. -/
theorem refines_dwarf (k0 : List Frame) :
    (F.mapping isa k0).toMapping.RefinesAt F.dwarfRel (fun _ => True) :=
  F.refines_dwarf isa k0

/-- The C function elaborates to the Core of `F` (`c.elaborates_to`). -/
theorem elaboration : Silmaril.Project.Shapes.C.ElaboratesTo Straight.ail "add3" F.cfn :=
  Straight.elaborates_add3

end StraightO0

/-! ## `straight.c`, `-O2`, `add3` (1 point) -/

namespace StraightO2

/-- The function and its code. -/
abbrev F : FnData := CompilesToExamples.Straight.O2.add3
/-- Edge 0: the segment from point 0 is simulated. -/
theorem edge_0 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 0 :=
  F.edgeValid_of_segment (Straight.O2.add3_segments 0) k0
/-- The whole mapping: every segment, at every point number. -/
theorem mapping_valid (k0 : List Frame) : (F.mapping isa k0).Valid :=
  fun k => F.edgeValid_of_segment (Straight.O2.add3_segments k) k0

/-- The translation: the machine, stopped at its first return, refines the Core run from every
System V call with a safe Core run. -/
theorem translation (k0 : List Frame) : (F.compilation isa k0).toProblem.Refines :=
  F.compilation_refines_of_segments isa k0 (fun _ => rfl) rfl Straight.O2.add3_segments

/-- Non-vacuity at the canonical entries: `c.compiles_to.canonical_entry` (one entry per argument
tuple, safe for some tuple). -/
theorem canonical :
    Silmaril.Project.Shapes.CompilesTo.CompilesToCanonical isa F.placement F.frame F.cfn :=
  Straight.O2.add3_canonical
/-- The System V entry exists: the placement can be entered for every argument tuple. -/
theorem abi : Silmaril.Project.Shapes.SysV.Enterable isa F.placement F.sig F.frame :=
  Straight.O2.add3_enterable

/-- The problem is not vacuous: a safe canonical Core entry is related to a System V entry. -/
theorem inhabited : (F.compilation isa []).toProblem.Inhabited :=
  F.compilation_inhabited isa (by decide) abi (by decide) (by decide +kernel) (by decide)
    (by decide +kernel) Straight.add3Args Straight.add3_args_safe

/-- The mapping refines the location relation at every point. -/
theorem refines_dwarf (k0 : List Frame) :
    (F.mapping isa k0).toMapping.RefinesAt F.dwarfRel (fun _ => True) :=
  F.refines_dwarf isa k0

/-- The C function elaborates to the Core of `F` (`c.elaborates_to`). -/
theorem elaboration : Silmaril.Project.Shapes.C.ElaboratesTo Straight.ail "add3" F.cfn :=
  Straight.elaborates_add3

end StraightO2

/-! ## `branch.c`, `-O0`, `max2` (5 points) -/

namespace BranchO0

/-- The function and its code. -/
abbrev F : FnData := CompilesToExamples.Branch.O0.max2
/-- Edge 0: the segment from point 0 is simulated. -/
theorem edge_0 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 0 :=
  F.edgeValid_of_segment (Branch.O0.max2_segments 0) k0
/-- Edge 1: the segment from point 1 is simulated. -/
theorem edge_1 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 1 :=
  F.edgeValid_of_segment (Branch.O0.max2_segments 1) k0
/-- Edge 2: the segment from point 2 is simulated. -/
theorem edge_2 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 2 :=
  F.edgeValid_of_segment (Branch.O0.max2_segments 2) k0
/-- Edge 3: the segment from point 3 is simulated. -/
theorem edge_3 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 3 :=
  F.edgeValid_of_segment (Branch.O0.max2_segments 3) k0
/-- Edge 4: the segment from point 4 is simulated. -/
theorem edge_4 (k0 : List Frame) : (F.mapping isa k0).EdgeValid 4 :=
  F.edgeValid_of_segment (Branch.O0.max2_segments 4) k0
/-- The whole mapping: every segment, at every point number. -/
theorem mapping_valid (k0 : List Frame) : (F.mapping isa k0).Valid :=
  fun k => F.edgeValid_of_segment (Branch.O0.max2_segments k) k0

/-- The translation: the machine, stopped at its first return, refines the Core run from every
System V call with a safe Core run. -/
theorem translation (k0 : List Frame) : (F.compilation isa k0).toProblem.Refines :=
  F.compilation_refines_of_segments isa k0 (fun _ => rfl) rfl Branch.O0.max2_segments

/-- Non-vacuity at the canonical entries: `c.compiles_to.canonical_entry` (one entry per argument
tuple, safe for some tuple). -/
theorem canonical :
    Silmaril.Project.Shapes.CompilesTo.CompilesToCanonical isa F.placement F.frame F.cfn :=
  Branch.O0.max2_canonical
/-- The System V entry exists: the placement can be entered for every argument tuple. -/
theorem abi : Silmaril.Project.Shapes.SysV.Enterable isa F.placement F.sig F.frame :=
  Branch.O0.max2_enterable

/-- The problem is not vacuous: a safe canonical Core entry is related to a System V entry. -/
theorem inhabited : (F.compilation isa []).toProblem.Inhabited :=
  F.compilation_inhabited isa (by decide) abi (by decide) (by decide +kernel) (by decide)
    (by decide +kernel) Branch.max2Args Branch.max2_args_safe

/-- The mapping refines the location relation at every point. -/
theorem refines_dwarf (k0 : List Frame) :
    (F.mapping isa k0).toMapping.RefinesAt F.dwarfRel (fun _ => True) :=
  F.refines_dwarf isa k0

/-- The C function elaborates to the Core of `F` (`c.elaborates_to`). -/
theorem elaboration : Silmaril.Project.Shapes.C.ElaboratesTo Branch.ail "max2" F.cfn :=
  Branch.elaborates_max2

end BranchO0

/-! ## `branch.c`, `-O2`, `max2` (1 point, its segment open) -/

namespace BranchO2

/-- The function and its code. -/
abbrev F : FnData := CompilesToExamples.Branch.O2.max2
/-- The System V entry exists: the placement can be entered for every argument tuple. -/
theorem abi : Silmaril.Project.Shapes.SysV.Enterable isa F.placement F.sig F.frame :=
  Silmaril.Project.Shapes.SysV.Enterable.of_fits (fun _ => trivial) (by decide) (by decide)
    (by decide)

/-- The problem is not vacuous: a safe canonical Core entry is related to a System V entry. -/
theorem inhabited : (F.compilation isa []).toProblem.Inhabited :=
  F.compilation_inhabited isa (by decide) abi (by decide) (by decide +kernel) (by decide)
    (by decide +kernel) Branch.max2Args Branch.max2_args_safe

/-- The mapping refines the location relation at every point. -/
theorem refines_dwarf (k0 : List Frame) :
    (F.mapping isa k0).toMapping.RefinesAt F.dwarfRel (fun _ => True) :=
  F.refines_dwarf isa k0

/-- The C function elaborates to the Core of `F` (`c.elaborates_to`). -/
theorem elaboration : Silmaril.Project.Shapes.C.ElaboratesTo Branch.ail "max2" F.cfn :=
  Branch.elaborates_max2

end BranchO2

end CompilesToExamples.Explorer

end
