module

public import Silmaril.Project.CompilesTo.Explorer.Defs
public import Silmaril.Compiler.Explorer.Thms
public import Silmaril.Project.CompilesTo.Thms
import Silmaril.Proofs.Project.CompilesTo.Explorer

/-!
# C functions as compilation problems: theorems

* `FnData.mapping_corr`: the mapping's correspondence is the function's `FnData.corr`, so a
  proved `FnData.Segment` is a valid edge (`FnData.edgeValid_of_segment`).
* `FnData.mapping_starts`: the mapping starts at the System V entry.
* `FnData.compilation_valid_of_segments`: every segment proved gives the compilation problem.
* `FnData.refines_dwarf`: the mapping refines the relation the DWARF comorphism generates, at
  every point. It is independent of the segments: it holds for every function, proved or not.

Proofs: `Silmaril.Proofs.Project.CompilesTo.Explorer`.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.Explorer
open Silmaril.Cerberus.Core.Dynamics

namespace FnData

/-- The mapping's correspondence is the function's correspondence. -/
theorem mapping_corr (F : FnData) (I : Model) (k0 : List Frame) :
    (F.mapping I k0).corr = F.corr I k0 := rfl

/-- **A proved segment is a valid edge**, in every caller continuation. -/
theorem edgeValid_of_segment (F : FnData) {I : Model} {k : Nat} (h : F.Segment I k)
    (k0 : List Frame) : (F.mapping I k0).EdgeValid k := h k0

/-- **The mapping starts at the System V entry**, when point `0` is the entry at offset `0` and
the model reads `rip` from the open state. -/
theorem mapping_starts (F : FnData) (I : Model) (k0 : List Frame)
    (hrip : ∀ m, (I.core m).rip = m.core.rip)
    (hp0 : F.points[0]? = some ⟨F.body, 0, .entry⟩) : (F.mapping I k0).Starts :=
  Silmaril.Proofs.Project.CompilesTo.Explorer.mapping_starts F I k0 hrip hp0

/-- **Every segment proved gives the compilation problem**: from every System V call whose Core
run is safe, the machine returns with the System V result of a value the Core returns. -/
theorem compilation_valid_of_segments (F : FnData) (I : Model) (k0 : List Frame)
    (hrip : ∀ m, (I.core m).rip = m.core.rip)
    (hp0 : F.points[0]? = some ⟨F.body, 0, .entry⟩) (h : ∀ k, F.Segment I k) :
    (F.compilation I k0).Valid :=
  Problem.valid_of_mapping _ (F.mapping_starts I k0 hrip hp0) fun k => h k k0

/-- **The mapping refines the DWARF relation** at every point: whenever Core and machine states
are related at a point, every C object with a value there has a value that it holds in Core and
that its DWARF frame location holds on the machine. -/
theorem refines_dwarf (F : FnData) (I : Model) (k0 : List Frame) :
    (F.mapping I k0).RefinesComorphism dwarf F.scope (fun _ => True) :=
  Silmaril.Proofs.Project.CompilesTo.Explorer.refines_dwarf F I k0

end FnData

end Silmaril.Project.CompilesTo

end
