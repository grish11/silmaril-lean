module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n : Nat}
variable {g : Graph P params results n 1} {roles : Roles P}
variable {m : Interpretation.{u,v,w} P}

theorem Recovered.laws (a : Recovered g roles) (laws : roles.Laws m) :
    a.certificate.Laws m :=
  ⟨a.zero.symm ▸ laws.zero, a.tick.symm ▸ laws.tick, a.negate.symm ▸ laws.negate⟩

/-- A recovered program preserves the ordered observations on every
successful finite execution, under the supplied opcode laws. -/
theorem Recovered.observe_of_exec (a : Recovered g roles) (laws : roles.Laws m)
    (input : Tuple m.Value params) (idx : Index 1) {output : Tuple m.Value results}
    (ran : Exec m a.certificate.revert input (some output)) :
    g.observe m (g.denote m input a.certificate.demandWellFounded) idx = output.map (fun _ => some) :=
  a.certificate.observe_of_exec (a.laws laws) input idx ran

/-- Inferred reversion realizes a certified first pass and ordered
observation using that same pass count as fuel. -/
theorem Recovered.runFuel_of_firstExit (a : Recovered g roles) (laws : roles.Laws m)
    (total : a.certificate.Total m) (input : Tuple m.Value params) (idx : Index 1) (k : Nat)
    {output : Tuple m.Value results}
    (pass : a.certificate.FirstExit m (g.denote m input a.certificate.demandWellFounded) idx k)
    (observed : g.observe m (g.denote m input a.certificate.demandWellFounded) idx =
      output.map (fun _ => some)) :
    a.certificate.runFuel m k input = some output :=
  a.certificate.runFuel_of_firstExit (a.laws laws) total input idx k pass observed

theorem Recovered.exec_iff_firstExit (a : Recovered g roles) (laws : roles.Laws m)
    (total : a.certificate.Total m) (input : Tuple m.Value params) (idx : Index 1)
    (output : Tuple m.Value results) :
    Exec m a.certificate.revert input (some output) ↔
      (∃ k, a.certificate.FirstExit m (g.denote m input a.certificate.demandWellFounded) idx k) ∧
      g.observe m (g.denote m input a.certificate.demandWellFounded) idx =
        output.map (fun _ => some) :=
  a.certificate.exec_iff_firstExit (a.laws laws) total input idx output

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Automatic
