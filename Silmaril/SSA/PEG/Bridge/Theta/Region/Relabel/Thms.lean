module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel.Defs
public import Silmaril.SSA.RVSDG.Theta.Institution.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.Relabel.Compiler

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel

open Simple.Revert.While.Region (Certificate)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Compiler (body)

variable {Data : Type} {P Q : InstructionSet.{0,0} Data}
variable {carried results : List (Ty Data)} {result : Ty Data} {n l : Nat}
variable {g : Graph P carried [result] n 1} {allowInvariant : Bool}

/-- The projection-reducing table map is Peggy's ordinary opcode relabelling. -/
theorem mapOps_eq (f : InstructionMap P Q) (g : Graph P carried results n l) :
    g.mapOps f = table f g :=
  Proofs.mapOps_eq f g

/-- The numbered compiler commutes with opcode relabelling, including the
dependent list of body signatures. -/
theorem compile_map (f : InstructionMap P Q) (cert : Certificate g allowInvariant) :
    (⟨(body (certificate f cert)).1, compile (certificate f cert)⟩ :
      Σ sigs, RVSDG.Theta.Graph (Opcode Q) (valuePorts carried) sigs) =
    ⟨(body cert).1, RVSDG.Theta.Institution.relabel (opcode f) (compile cert)⟩ :=
  Proofs.compile_map f cert

end Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel
