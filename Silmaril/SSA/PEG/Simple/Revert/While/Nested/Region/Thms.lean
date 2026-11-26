module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Nested.Region.Correctness

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer inner : List (Ty Data)} {result : Ty Data} {n l : Nat}
variable {g : Graph P outer [result] n l} {m : Interpretation.{u,v,w} P}

theorem Accepted.demandWellFounded (a : Accepted g inner) : WellFounded g.Demand :=
  g.demandWellFounded_of_check a.rank a.ranked

/-- A fresh activation starts at child index zero with the current outer
captures. Its completed SIMPLE store realizes the child evals at one
least pass and retains the old captures for the outer commit. -/
theorem Accepted.activation_observation (a : Accepted g inner)
    (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (input : Tuple m.Value outer) (base : Index l)
    {old : Tuple m.Value outer} {out : Tuple m.Value (inner ++ outer)}
    (captures : a.Captures m (g.denote m input a.demandWellFounded) base old)
    (ran : Exec m a.activate old (some out)) :
    ∃ k, a.ChildObservation m (g.denote m input a.demandWellFounded) base k out :=
  Proofs.activation a neg (g.denote_solves m input a.demandWellFounded) base captures ran

/-- The outer trace supplies the capture premise for each activation.
Every successful finite nested execution returns the original PEG eval
at the outer first pass and its defined prefix. -/
theorem Accepted.observe_of_returns (a : Accepted g inner)
    (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (input : Tuple m.Value outer) (i : Index l)
    {value : m.Value result} (returned : a.revert.Returns m input value) :
    g.observe m (g.denote m input a.demandWellFounded) i = .cons (some value) .nil :=
  Proofs.observe_of_returns a neg (g.denote_solves m input a.demandWellFounded) i returned

theorem Accepted.activate_of_runFuel (a : Accepted g inner) (fuel : Nat)
    {old : Tuple m.Value outer} {out : Tuple m.Value (inner ++ outer)}
    (ran : a.activateFuel m fuel old = some out) : Exec m a.activate old (some out) :=
  Proofs.activate_of_runFuel a fuel ran

theorem Accepted.returns_of_runFuel (a : Accepted g inner) (outerFuel childFuel : Nat)
    {input : Tuple m.Value outer} {value : m.Value result}
    (ran : a.runFuel m outerFuel childFuel input = some value) : a.revert.Returns m input value :=
  Proofs.returns_of_runFuel a outerFuel childFuel ran

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region
