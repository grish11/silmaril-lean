module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle.Defs

/-! # Finite cost selection with ordered SIMPLE returns -/

@[expose] public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle

open PEG
open PEG.Simple.Revert.While
open EPEG (Classes)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {source : Graph P params (result :: rest) n 1}

abbrev Accepted (source : Graph P params (result :: rest) n 1) (classes : Classes n) :=
  Checked source classes (fun c => Region.Bundle.Certificate c.graph)

def Accepted.output {classes : Classes n} (accepted : Accepted source classes) :
    PEG.Simple.Stmt P true params (result :: rest) :=
  accepted.reversion.revert

variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

def check (classes : Classes n) (candidate : Candidate source) : Option (Accepted source classes) :=
  candidate.checkWith classes (fun c => Region.Bundle.extract c.graph)

def select (classes : Classes n) (cost : Candidate source → Nat) (pool : List (Candidate source)) :
    Option (Accepted source classes) :=
  Cost.selectWith classes (fun c => Region.Bundle.extract c.graph) cost pool

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle
