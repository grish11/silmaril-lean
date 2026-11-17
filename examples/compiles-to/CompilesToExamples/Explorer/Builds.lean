module

public import CompilesToExamples.Straight.Thms
public import CompilesToExamples.Branch.Thms
public import Silmaril.Project.CompilesTo.Explorer.Thms

/-!
# The compiles-to examples as compilation problems

The `straight.c` and `branch.c` builds of `examples/compiles-to` (gcc 13.3.0, pinned by digest)
read through `Silmaril.Compiler.Explorer`: per build, each edge of the mapping, the whole
mapping, the translation and the refinement of the DWARF relation, each its own theorem, so that
`tools/compiler-explorer` can check each one by its statement.

Every theorem here restates a result of the generated proof modules
(`CompilesToExamples.<File>.Proofs.*`) in the explorer's vocabulary; none adds an assumption.
`branch.c` at `-O2` (one point, `cmp; mov; cmovge; ret`) has no proved segment: its edge, its
mapping and its translation stay open (`Task.max2_seg_0`). Its mapping still refines the DWARF
relation (`BranchO2.refines_dwarf`): the refinement does not depend on the segments.

What stays open for every build: `Task.<f>_safe` (safety from every Core entry), without which
the translation is proved only for safe entries and could be vacuous; the canonical-entry rows
(`<Build>.<f>_canonical`) show non-vacuity for one entry per argument tuple.
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

/-- The translation: from every System V call with a safe Core run, the machine returns the
Core result. -/
theorem translation_valid (k0 : List Frame) : (F.compilation isa k0).Valid :=
  F.compilation_valid_of_segments isa k0 (fun _ => rfl) rfl Straight.O0.add3_segments

/-- The mapping refines the DWARF relation at every point. -/
theorem refines_dwarf (k0 : List Frame) :
    (F.mapping isa k0).RefinesComorphism dwarf F.scope (fun _ => True) :=
  F.refines_dwarf isa k0

/-- Non-vacuity at the canonical entries: `c.compiles_to.canonical_entry` (one entry per argument
tuple, safe for some tuple). -/
theorem canonical :
    Silmaril.Project.Shapes.CompilesTo.CompilesToCanonical isa F.placement F.frame F.cfn :=
  Straight.O0.add3_canonical

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

/-- The translation: from every System V call with a safe Core run, the machine returns the
Core result. -/
theorem translation_valid (k0 : List Frame) : (F.compilation isa k0).Valid :=
  F.compilation_valid_of_segments isa k0 (fun _ => rfl) rfl Straight.O2.add3_segments

/-- The mapping refines the DWARF relation at every point. -/
theorem refines_dwarf (k0 : List Frame) :
    (F.mapping isa k0).RefinesComorphism dwarf F.scope (fun _ => True) :=
  F.refines_dwarf isa k0

/-- Non-vacuity at the canonical entries: `c.compiles_to.canonical_entry` (one entry per argument
tuple, safe for some tuple). -/
theorem canonical :
    Silmaril.Project.Shapes.CompilesTo.CompilesToCanonical isa F.placement F.frame F.cfn :=
  Straight.O2.add3_canonical

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

/-- The translation: from every System V call with a safe Core run, the machine returns the
Core result. -/
theorem translation_valid (k0 : List Frame) : (F.compilation isa k0).Valid :=
  F.compilation_valid_of_segments isa k0 (fun _ => rfl) rfl Branch.O0.max2_segments

/-- The mapping refines the DWARF relation at every point. -/
theorem refines_dwarf (k0 : List Frame) :
    (F.mapping isa k0).RefinesComorphism dwarf F.scope (fun _ => True) :=
  F.refines_dwarf isa k0

/-- Non-vacuity at the canonical entries: `c.compiles_to.canonical_entry` (one entry per argument
tuple, safe for some tuple). -/
theorem canonical :
    Silmaril.Project.Shapes.CompilesTo.CompilesToCanonical isa F.placement F.frame F.cfn :=
  Branch.O0.max2_canonical

/-- The C function elaborates to the Core of `F` (`c.elaborates_to`). -/
theorem elaboration : Silmaril.Project.Shapes.C.ElaboratesTo Branch.ail "max2" F.cfn :=
  Branch.elaborates_max2

end BranchO0

/-! ## `branch.c`, `-O2`, `max2` (1 point, its segment open) -/

namespace BranchO2

/-- The function and its code. -/
abbrev F : FnData := CompilesToExamples.Branch.O2.max2

/-- The mapping refines the DWARF relation at every point, although no segment is proved. -/
theorem refines_dwarf (k0 : List Frame) :
    (F.mapping isa k0).RefinesComorphism dwarf F.scope (fun _ => True) :=
  F.refines_dwarf isa k0

/-- The C function elaborates to the Core of `F` (`c.elaborates_to`). -/
theorem elaboration : Silmaril.Project.Shapes.C.ElaboratesTo Branch.ail "max2" F.cfn :=
  Branch.elaborates_max2

end BranchO2

end CompilesToExamples.Explorer

end
