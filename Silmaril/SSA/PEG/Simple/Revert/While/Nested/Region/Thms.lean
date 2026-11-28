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
  (Proofs.exits_and_observe a neg (g.denote_solves m input a.demandWellFounded) i returned).2

/-- Successful nested execution certifies the least outer pass, every
required child activation pass, and the ordered return. -/
theorem Accepted.exits_and_observe_of_returns (a : Accepted g inner)
    (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (input : Tuple m.Value outer) (base : Index l)
    {value : m.Value result} (returned : a.revert.Returns m input value) :
    (∃ count, a.FirstExits m (g.denote m input a.demandWellFounded) base count) ∧
      g.observe m (g.denote m input a.demandWellFounded) base = .cons (some value) .nil :=
  Proofs.exits_and_observe a neg (g.denote_solves m input a.demandWellFounded) base returned

theorem Accepted.activate_of_runFuel (a : Accepted g inner) (fuel : Nat)
    {old : Tuple m.Value outer} {out : Tuple m.Value (inner ++ outer)}
    (ran : a.activateFuel m fuel old = some out) : Exec m a.activate old (some out) :=
  Proofs.activate_of_runFuel a fuel ran

theorem Accepted.returns_of_runFuel (a : Accepted g inner) (outerFuel childFuel : Nat)
    {input : Tuple m.Value outer} {value : m.Value result}
    (ran : a.runFuel m outerFuel childFuel input = some value) : a.revert.Returns m input value :=
  Proofs.returns_of_runFuel a outerFuel childFuel ran

/-- Totality discharges the primitive schedule premises. Finite child
passes are separate evidence. -/
theorem Accepted.definedSlices_of_total (a : Accepted g inner) (values : g.Valuation m)
    (total : ∀ {ins out} (op : P ins out) args, ∃ val, m.run op args = some val) :
    a.DefinedSlices m values :=
  Proofs.defined_of_total a total

/-- A definite child first pass constructs an invocation on the current
captures and the full commit entry store at that pass. -/
theorem Accepted.activate_of_firstExit (a : Accepted g inner)
    (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (input : Tuple m.Value outer)
    (slices : a.DefinedSlices m (g.denote m input a.demandWellFounded))
    (base : Index l) (trips : Nat) {old : Tuple m.Value outer}
    (captures : a.Captures m (g.denote m input a.demandWellFounded) base old)
    (picked : Rules.readRef (g.denote m input a.demandWellFounded) a.descriptor.childPass base =
      some ⟨trips⟩) :
    ∃ output, Exec m a.activate old (some output) ∧
      a.ChildObservation m (g.denote m input a.demandWellFounded) base trips output :=
  Proofs.activate_of_firstExit a neg (g.denote_solves m input a.demandWellFounded)
    slices base trips captures picked

/-- The outer pass gives the exact finite outer trace length. Each
continuing step consumes the child pass at that outer iteration. -/
theorem Accepted.trace_of_exits (a : Accepted g inner)
    (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (input : Tuple m.Value outer)
    (slices : a.DefinedSlices m (g.denote m input a.demandWellFounded))
    (base : Index l) {count : Nat}
    (exits : a.FirstExits m (g.denote m input a.demandWellFounded) base count) :
    ∃ start final, Exec m a.outerGuard.lower.enableWhile input (some start) ∧
      WhileTrace m (continueTest a.descriptor.negate) a.body count start final :=
  Proofs.trace_of_exits a neg (g.denote_solves m input a.demandWellFounded) slices base exits

theorem Accepted.returns_of_exits (a : Accepted g inner)
    (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (input : Tuple m.Value outer)
    (slices : a.DefinedSlices m (g.denote m input a.demandWellFounded))
    (base : Index l) {count : Nat}
    (exits : a.FirstExits m (g.denote m input a.demandWellFounded) base count)
    {value : m.Value result}
    (observed : g.observe m (g.denote m input a.demandWellFounded) base = .cons (some value) .nil) :
    a.revert.Returns m input value :=
  Proofs.returns_of_exits a neg (g.denote_solves m input a.demandWellFounded) slices base exits observed

/-- Successful nested execution gives every required finite pass and the
defined return. Slice definedness is needed to construct the execution. -/
theorem Accepted.returns_iff_exits (a : Accepted g inner)
    (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (input : Tuple m.Value outer)
    (slices : a.DefinedSlices m (g.denote m input a.demandWellFounded))
    (base : Index l) (value : m.Value result) :
    a.revert.Returns m input value ↔
      (∃ count, a.FirstExits m (g.denote m input a.demandWellFounded) base count) ∧
        g.observe m (g.denote m input a.demandWellFounded) base = .cons (some value) .nil :=
  ⟨Proofs.exits_and_observe a neg (g.denote_solves m input a.demandWellFounded) base,
    fun ⟨⟨_, exits⟩, observed⟩ => a.returns_of_exits neg input slices base exits observed⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region
