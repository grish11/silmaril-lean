module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {results : List (Ty Data)} {n : Nat}
variable {g : Graph P [] results n 1} {roles : Roles P}
variable {m : Interpretation.{u,v,w} P}

theorem Recovered.laws (a : Recovered g roles) (laws : roles.Laws m) :
    a.certificate.Laws m :=
  ⟨a.zero.symm ▸ laws.zero, a.tick.symm ▸ laws.tick, a.negate.symm ▸ laws.negate⟩

/-- A recovered program preserves the ordered observations on every
successful finite execution, under the supplied opcode laws. -/
theorem Recovered.observe_of_exec (a : Recovered g roles) (laws : roles.Laws m)
    (idx : Index 1) {output : Tuple m.Value results}
    (ran : Exec m a.certificate.revert .nil (some output)) :
    g.observe m (g.denote m .nil a.certificate.demandWellFounded) idx = output.map (fun _ => some) :=
  a.certificate.observe_of_exec (a.laws laws) idx ran

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic
