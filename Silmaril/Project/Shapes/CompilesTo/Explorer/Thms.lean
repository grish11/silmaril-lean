module

public import Silmaril.Project.Shapes.CompilesTo.Explorer.Defs
public import Silmaril.Compiler.Explorer.Det.Thms
public import Silmaril.Project.Shapes.CompilesTo.Thms
import Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer

/-!
# C functions as compilation problems: theorems

* `FnData.mapping_corr`: the mapping's correspondence is `FnData.corr`, so a proved
  `FnData.Segment` is a valid edge (`FnData.edgeValid_of_segment`).
* `FnData.compilation_valid_of_segments`: every segment proved gives the deterministic problem,
  to the first return; `FnData.compilation_refines_of_segments` gives the generic, backward
  refinement `(F.compilation I k0).toProblem.Refines`.
* `FnData.compilation_inhabited`: the problem is not vacuous: for the empty caller continuation,
  a canonical Core entry that is safe and a machine entry the placement admits are related.
* `FnData.refines_dwarf`: the mapping refines the relation the location semi-comorphism
  generates, at every point, for every function (proved or not).

Proofs: `Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer`.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.Explorer
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.X86.SystemV.CApi (Arguments)

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
  Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer.mapping_starts F I k0 hrip hp0

/-- **Every segment proved gives the problem**, to the first return. -/
theorem compilation_valid_of_segments (F : FnData) (I : Model) (k0 : List Frame)
    (hrip : ∀ m, (I.core m).rip = m.core.rip)
    (hp0 : F.points[0]? = some ⟨F.body, 0, .entry⟩) (h : ∀ k, F.Segment I k) :
    (F.compilation I k0).Valid :=
  (F.mapping I k0).valid_of_segments (F.mapping_starts I k0 hrip hp0) (fun k => h k k0)
    (F.notFinal I k0)

/-- **Every segment proved gives the refinement**: from every System V call whose Core run is
safe, every run of the machine to its first return is safe, finite, never stuck, and returns the
System V result of a value the Core returns. -/
theorem compilation_refines_of_segments (F : FnData) (I : Model) (k0 : List Frame)
    (hrip : ∀ m, (I.core m).rip = m.core.rip)
    (hp0 : F.points[0]? = some ⟨F.body, 0, .entry⟩) (h : ∀ k, F.Segment I k) :
    (F.compilation I k0).toProblem.Refines :=
  (F.compilation I k0).refines_of_valid (F.compilation_valid_of_segments I k0 hrip hp0 h)

/-- **The problem is not vacuous** (empty caller continuation): the canonical entry with the
arguments `a`, safe, is related to a System V entry the placement admits. -/
theorem compilation_inhabited (F : FnData) (I : Model) (haddr : F.addr < 2 ^ 64)
    (hen : Silmaril.Project.Shapes.SysV.Enterable I F.placement F.sig F.frame)
    (hint : ∀ k ∈ F.sig.arguments, k = .int32) (hlen : F.params.length = F.sig.arguments.length)
    (hsix : F.sig.arguments.length ≤ 6) (hnd : (F.params.map (·.1.key)).Nodup)
    (a : Arguments F.sig.arguments) (hsafe : (F.source []).Safe (F.cfn.canonicalEntry a)) :
    (F.compilation I []).toProblem.Inhabited :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer.compilation_inhabited F I haddr hen hint hlen
    hsix hnd a hsafe

/-- **The mapping refines the location relation** at every point: whenever Core and machine
states are related at a point, every C object with a value there has a value that it holds in
Core and that its frame slot holds on the machine. -/
theorem refines_dwarf (F : FnData) (I : Model) (k0 : List Frame) :
    (F.mapping I k0).toMapping.RefinesAt F.dwarfRel (fun _ => True) :=
  Silmaril.Proofs.Project.Shapes.CompilesTo.Explorer.refines_dwarf F I k0

end FnData

end Silmaril.Project.CompilesTo

end
