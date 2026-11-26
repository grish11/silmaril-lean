module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Correctness

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
/-- Replay a successful checked slice at a fixed Figure 11 index.
The loop-key space is arbitrary because the schedule introduces only
primitive bindings, projections, and checked lazy branches. -/
theorem Schedule.realizes_lower {l : Nat} {graph : Graph P carried [result] n l}
    {m : Interpretation.{u,v,w} P} {input : Tuple m.Value carried} {values : graph.Valuation m}
    {allowBranch : Bool} {vars outs : List (Ty Data)}
    {scope : Tuple (Ref graph.sort) vars} {roots : Tuple (Ref graph.sort) outs}
    (code : Schedule graph allowBranch roots scope) (solves : graph.Solves m input values)
    {idx : Index l} {store : Tuple m.Value vars} {final : Tuple m.Value outs}
    (entry : Schedule.Realizes m values idx scope store)
    (ran : code.lower.runLoopFree m store = some final) :
    Schedule.Realizes m values idx roots final :=
  Proofs.schedule code solves entry ran

variable {g : Graph P carried [result] n 1}
variable {allowInvariant allowBranch : Bool}
variable (cert : Certificate g allowInvariant allowBranch) (m : Interpretation.{u,v,w} P) (input : Tuple m.Value carried)

theorem Certificate.demandWellFounded (cert : Certificate g allowInvariant allowBranch) : WellFounded g.Demand :=
  g.demandWellFounded_of_check cert.rank cert.ranked

theorem Certificate.runFuel_returns (fuel : Nat) {value : m.Value result}
    (ran : cert.runFuel m fuel input = some value) : cert.revert.Returns m input value :=
  Proofs.runFuel_returns cert fuel ran

/-- A single successful reversion trace identifies the first pass and the
defined Figure 11 prefixes at all carried ports simultaneously. -/
theorem Certificate.traceObservation
    (neg : ∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {k : Nat} {start final : Tuple m.Value (.bool :: carried)}
    (guard : cert.guard.lower.runLoopFree m input = some start)
    (trace : WhileTrace m (.var .head) cert.body.enableWhile k start final) :
    cert.TraceObservation m (g.denote m input cert.demandWellFounded) idx k final :=
  Proofs.traceObservation cert (g.denote_solves m input _) neg idx guard trace

/-- Every successful emitted SIMPLE execution defines the original PEG
return. The negation opcode implements the exit test. -/
theorem Certificate.observe_of_returns
    (neg : ∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {value : m.Value result} (ran : cert.revert.Returns m input value) :
    g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil :=
  Proofs.observe_of_returns cert (g.denote_solves m input _) neg idx ran

/-- A defined PEG exit supplies the exact pass count and the eval prefix.
The full update vector and the guard must be total on defined stores. -/
theorem Certificate.exitWitness_of_defined (total : cert.Total m)
    (neg : ∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {value : m.Value result}
    (defined : g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil) :
    ∃ k start final, cert.guard.lower.runLoopFree m input = some start ∧
      cert.ExitWitness m (g.denote m input cert.demandWellFounded) idx k start final value :=
  Proofs.exitWitness_of_defined cert (g.denote_solves m input _) neg total idx defined

/-- Exact correspondence of successful SIMPLE returns and defined original
Figure 11 observations under the totality and negation premises. -/
theorem Certificate.returns_iff_observe (total : cert.Total m)
    (neg : ∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) (value : m.Value result) :
    cert.revert.Returns m input value ↔
      g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil := by
  refine ⟨cert.observe_of_returns m input neg idx, fun defined => ?_⟩
  obtain ⟨_, _, _, guard, exit⟩ := cert.exitWitness_of_defined m input total neg idx defined
  exact Proofs.returns_of_exit cert guard exit

theorem Certificate.runFuel_of_defined (total : cert.Total m)
    (neg : ∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {value : m.Value result}
    (defined : g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil) :
    ∃ k, cert.runFuel m k input = some value ∧
      cert.descriptor.pass.read m.carrier
        (g.denote m input cert.demandWellFounded (cert.descriptor.pass.id, idx)) = some ⟨k⟩ := by
  obtain ⟨k, _, _, guard, exit⟩ := cert.exitWitness_of_defined m input total neg idx defined
  exact ⟨k, Proofs.runFuel_of_exit cert guard exit, exit.pass⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Region
