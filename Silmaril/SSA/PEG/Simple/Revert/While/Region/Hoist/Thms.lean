module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
public import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Hoist

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1}
variable {m : Interpretation.{u,v,w} P} {input : Tuple m.Value carried}

theorem Site.invariantAt {d : Descriptor g} {i : Fin n} (site : Site d i) :
    Rules.InvariantAt g 0 i :=
  Proofs.invariantAt site

/-- A defined update root at a single iteration supplies a defined shared
value for every iteration. Both the same-index MustEval witness and the
all-indices invariance theorem are required. -/
theorem Site.cache_of_defined {d : Descriptor g} {i : Fin n} (site : Site d i)
    (wf : WellFounded g.Demand) {values : g.Valuation m} (solves : g.Solves m input values)
    (idx : Index 1)
    (ready : (values ((d.next.get (portAt carried site.updateSlot)).id, idx)).isSome) :
    ∃ cache : m.Value (g.sort i), ∀ atIndex,
      Rules.readRef values (Ref.ofId g.sort i) atIndex = some cache :=
  Proofs.cache_of_defined site wf solves idx ready

/-- The finite trace supplies successful guards and whole updates at their
actual stores. Its first pass and all carried eval prefixes refer to the
original Figure 11 graph. The emitted code also returns on the zero-step
trace, which has no invariant-evaluation obligation. -/
theorem Accepted.trace_placement (a : Accepted g)
    (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {steps : Nat} {start final : Tuple m.Value (.bool :: carried)}
    (guard : a.guard.lower.runLoopFree m input = some start)
    (trace : WhileTrace m (.var .head) a.base.body.enableWhile steps start final) :
    a.revert.Returns m input (final.get (.tail a.descriptor.returnSlot)) ∧
      a.base.TraceObservation m
        (g.denote m input a.base.demandWellFounded) idx steps final :=
  ⟨Proofs.returns_of_trace a (g.denote_solves m input a.base.demandWellFounded) guard trace,
    a.base.traceObservation m input neg idx guard trace⟩

theorem Accepted.returns_of_returns (a : Accepted g) {value : m.Value result}
    (ran : a.base.revert.Returns m input value) : a.revert.Returns m input value :=
  Proofs.returns_of_returns a ran

/-- Each successful reference return is also a successful emitted return
and a defined observation of the original PEG under the negation law. -/
theorem Accepted.preserves (a : Accepted g)
    (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {value : m.Value result} (ran : a.base.revert.Returns m input value) :
    a.revert.Returns m input value ∧
      g.observe m (g.denote m input a.base.demandWellFounded) idx = .cons (some value) .nil :=
  ⟨a.returns_of_returns ran, a.base.observe_of_returns m input neg idx ran⟩

theorem Accepted.runFuel_returns (a : Accepted g) (fuel : Nat) {value : m.Value result}
    (ran : a.runFuel m fuel input = some value) : a.revert.Returns m input value :=
  Proofs.runFuel_returns a fuel ran

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist
