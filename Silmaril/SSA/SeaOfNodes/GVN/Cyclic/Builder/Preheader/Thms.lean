module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Seed
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Prepare
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Correctness
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Restorable
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader

open Diamond (Ty ValueSort dataPorts sortValue)
open Activation (Inputs inputSlot)
open GVN.WordNumber (entryKeys numbering)
open GVN.WordNumber.Intern (Agrees)
open Pure.SubZero (Opcode model word)
open RVSDG (Port)
open scoped Pure.WordNormalize

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit} {loop : Native inputs carried entrySigs headerSigs out}
variable {result : Deletion.DeletedLoop Opcode inputs carried entrySigs out}

/-- The IDs at the actual preheader exit decode in a single duplicate-free table. -/
theorem number_agrees (loop : Native inputs carried entrySigs headerSigs out) :
    let bank := number loop
    bank.table.Nodup ∧ Agrees bank.table bank.entry bank.locals (entryKeys inputs)
      (loop.preheader.eval (numbering (dataPorts inputs)) (entryKeys inputs) PUnit.unit) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.number_agrees loop

/-- Equal preheader IDs imply equal values in the native initial latch tuple for every input. -/
theorem equal_lane_ids (lhs rhs : Port carried word) (same : laneId loop (number loop) lhs = laneId loop (number loop) rhs)
    (input : Inputs model inputs) :
    (loop.initial model input).get (inputSlot lhs) = (loop.initial model input).get (inputSlot rhs) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.equal_lane_ids lhs rhs same input

/-- The builder receives the same capture position exactly for equal same-table word IDs. -/
theorem canonical_word_iff (bank : Bank inputs entrySigs) (lhs rhs : Port carried word) :
    canonicalLane loop bank lhs = canonicalLane loop bank rhs ↔ laneId loop bank lhs = laneId loop bank rhs :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.canonical_word_iff bank lhs rhs

/-- Preparing the view reads precisely the original simultaneous entry latch tuple. -/
theorem prepare_initial (input : Inputs model inputs) :
    (prepare loop).initial model (preparedInput loop input) = loop.initial model input :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.prepare_initial input

/-- The prepared header keeps the guard, exit word and every feedback field in order. -/
theorem prepare_packet (input : Inputs model inputs) (old : Inputs model carried) :
    let args := Loop.appendTuple old input
    let expanded := Loop.appendTuple old (preparedInput loop input)
    (observations (prepare loop)).read expanded ((prepare loop).header.eval model expanded PUnit.unit) =
      (observations loop).read args (loop.header.eval model args PUnit.unit) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.prepare_packet input old

/-- Same-class Phi vertices have the same capture position and relabeled
feedback occurrence. Either difference rules out a merge. -/
theorem normalized_phi_occurrences (built : Built (prepare loop)) (i j : Vertex (prepare loop))
    (entry₁ : Port (carried ++ inputs) (sorts (prepare loop) i))
    (entry₂ : Port (carried ++ inputs) (sorts (prepare loop) j))
    (back₁ : Source (carried ++ inputs) (sorts (prepare loop)) (sorts (prepare loop) i))
    (back₂ : Source (carried ++ inputs) (sorts (prepare loop)) (sorts (prepare loop) j))
    (shape₁ : built.graph.node i = .phi entry₁ back₁) (shape₂ : built.graph.node j = .phi entry₂ back₂)
    (same : FixedPoint.normalize built.graph i = FixedPoint.normalize built.graph j) :
    entry₁.index = entry₂.index ∧ back₁.address.relabel (FixedPoint.normalize built.graph) =
      back₂.address.relabel (FixedPoint.normalize built.graph) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.normalized_phi_occurrences
    built i j entry₁ entry₂ back₁ back₂ shape₁ shape₂ same

/-- Preparing any native loop in this profile produces a direct-entry
header that the existing builder accepts, including after restoration. -/
theorem prepare_builds (loop : Native inputs carried entrySigs headerSigs out) :
    ∃ built, build? (prepare loop) = some built :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.prepare_builds loop

/-- A successful native result comes from the existing builder and pass and
then passes the checked removal of the temporary capture arguments. -/
theorem optimize_witness (accepted : optimize? loop = some result) :
    ∃ built : Built (prepare loop), ∃ edited, build? (prepare loop) = some built ∧
      Pass.step? built.view = some edited ∧ restore? loop edited = some result :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.optimize_witness accepted

/-- Every accepted proposal emitted by the pass for a prepared native
header can drop all temporary capture arguments. -/
theorem proposal_restores (built : Built (prepare loop)) {proposal : Pass.Proposal (prepare loop) (sorts (prepare loop))}
    {edited : Deletion.DeletedLoop Opcode (carried ++ inputs) carried [] out}
    (member : proposal ∈ Pass.proposals built.view)
    (accepted : Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal = some edited) :
    ∃ result, restore? loop edited = some result :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.proposal_restores built member accepted

/-- Selecting the first accepted shrinking step and checking restoration
gives the same native result as checking restoration inside the ordered scan. -/
theorem optimize_eq_scan (built : Built (prepare loop)) (builtEq : build? (prepare loop) = some built) :
    optimize? loop = (Pass.proposals built.view).findSome? (fun proposal =>
      (Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal).bind (restore? loop)) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.optimize_eq_scan built builtEq

/-- Once building succeeds, failure excludes every accepted proposal
in that view's enumeration. -/
theorem optimize_none_iff (built : Built (prepare loop)) (builtEq : build? (prepare loop) = some built) :
    optimize? loop = none ↔
      ∀ proposal ∈ Pass.proposals built.view, Pass.tryProposal? built.view (FixedPoint.normalize built.graph) proposal = none :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.optimize_none_iff built builtEq

theorem optimize_entry (accepted : optimize? loop = some result) :
    result.graph.preheader = loop.preheader ∧ result.graph.phiInputs .entry = loop.phiInputs .entry :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.optimize_entry accepted

theorem optimize_count (accepted : optimize? loop = some result) :
    result.headerSigs.length + 1 = headerSigs.length :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.optimize_count accepted

/-- The original simultaneous entry tuple satisfies the prepared view's invariant. -/
theorem initial_agrees (built : Built (prepare loop)) (input : Inputs model inputs) :
    built.view.LatchesAgree (FixedPoint.normalize built.graph) model
      (loop.initial model input) (loop.initial model input) :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.initial_agrees built input

/-- The original-interface rewrite preserves each reached activation's
selected outcome, including the complete feedback tuple, under the existing
cyclic latch invariant. The prepared entry establishes this invariant. -/
theorem optimize_activation (accepted : optimize? loop = some result) {built : Built (prepare loop)}
    (builtEq : build? (prepare loop) = some built)
    (input : Inputs model inputs) (old : Inputs model carried)
    (invariant : built.view.LatchesAgree (FixedPoint.normalize built.graph) model old old) :
    result.graph.step model input old = loop.step model input old :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.optimize_activation accepted builtEq input old invariant

theorem optimize_evalBackedges (accepted : optimize? loop = some result) (input : Inputs model inputs) (budget : Nat) :
    result.graph.evalBackedges model budget input = loop.evalBackedges model budget input :=
  Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.optimize_eval accepted input budget

theorem optimize_returns (accepted : optimize? loop = some result)
    (input : Inputs model inputs) (value : sortValue model.value out) :
    result.graph.Returns model input value ↔ loop.Returns model input value := by
  simp only [Loop.Graph.returns_iff_evalBackedges, optimize_evalBackedges accepted input]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader
