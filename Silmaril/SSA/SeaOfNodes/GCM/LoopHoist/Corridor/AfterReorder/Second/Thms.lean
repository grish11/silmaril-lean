module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg)
open Silmaril.MLIR.Pure (Operands)
open Header.Earlier (operations)
open Header.Sequence (State)
open Loop.MLIR.CF (Program TargetOp evalOp lower)

variable {Input Γ extra : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {first : AfterReorder.Plan} {consumerOrigin : Nat} {prepared : Prepared Input carried result}
variable {candidate : Candidate Input saved carried result extra}
variable {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}

/-- Every captured definition cut is a necessary lower bound, and their
maximum is sufficient for local operand order. -/
theorem Candidate.earliestCut_le_iff {cut : Nat} :
    candidate.earliestCut ≤ cut ↔ ∀ operand ∈ candidate.operands, operand.cut ≤ cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.earliestCut_le_iff

/-- The sites used to compute the bound come from the capture's typed references. -/
theorem findCaptured?_sites {index cursor : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    (found : findCaptured? index cursor origins code = some candidate) :
    candidate.operands = prefixSites candidate.inputs :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.findCaptured?_sites found

/-- In an actual typed entry prefix, the computed interval includes exactly
the prefix cuts whose operands are valid and available on the current CFG. -/
theorem findCaptured?_operandCut_iff {index cut : Nat}
    {leading : Saved.Prefix Input ((extra ++ [saved]) ++ Input)}
    {tail : Block TargetOp (Label saved carried result extra) ((extra ++ [saved]) ++ Input) [result]}
    (split : Saved.splitPrefix? cfg.entry (extra ++ [saved]) = some (leading, tail))
    (found : findCaptured? index 0 (Saved.origins (extra ++ [saved])) (cfg.block .header) = some candidate) :
    candidate.operandCut? cut = true ↔ cut ≤ (extra ++ [saved]).length ∧
      (Point.mk none cut).Valid cfg ∧
      ∀ operand ∈ candidate.operands, operand.Valid cfg ∧ operand.AvailableAt cfg ⟨none, cut⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.findCaptured?_operandCut_iff split found

/-- Full checking retains the ordinary and exact Φ use constraints. -/
theorem checkPrefixCut_legal {cut : Nat} (accepted : checkPrefixCut cfg candidate cut = true) :
    Legal cfg candidate.operands candidate.uses ⟨none, cut⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.checkPrefixCut_legal accepted

/-- The interval guard preserves the existing append check on every actual capture. -/
theorem findCaptured?_checkConsumer_eq {index cursor : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    (found : findCaptured? index cursor origins code = some candidate) :
    checkConsumer cfg candidate =
      (let _ := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
       Dominance.Placement.checkCut cfg intermediateBlocks candidate.operands candidate.uses
         ⟨none, (extra ++ [saved]).length⟩) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.findCaptured?_checkConsumer_eq found

/-- The handoff retains the exact intermediate CFG and resolves its current origin order. -/
theorem prepareOn?_spec {intermediate : Output Input carried result} {origins : List Nat}
    (accepted : prepareOn? intermediate origins consumerOrigin = some prepared) :
    prepared.intermediate = intermediate ∧ prepared.origins = origins ∧
    prepared.origins.idxOf? consumerOrigin = some prepared.index ∧
    findCaptured? prepared.index 0 savedOrigins (prepared.intermediate.2.block .header) =
      some prepared.consumer ∧ checkConsumer prepared.intermediate.2 prepared.consumer = true :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepareOn?_spec accepted

/-- The first hoist removes exactly its resolved operation from header order. -/
theorem hoistCodeWith?_operations
    {entry : Block TargetOp (SourceLabel carried result) Input [result]}
    {header : Block TargetOp (SourceLabel carried result) (carried :: Input) [result]}
    {choose : List (Point (SourceLabel carried result)) → List (Use (SourceLabel carried result)) →
      Option (Point (SourceLabel carried result))}
    {index : Nat} {cut : Point (SourceLabel carried result)} {output : Output Input carried result}
    (moved : hoistCodeWith? entry header index choose = some (cut, output)) :
    operations (output.2.block .header) = (operations header).eraseIdx index :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.hoistCodeWith?_operations moved

/-- The enlarged scanner returns the identical typed binding and sites
for every successful saved-dependent capture. -/
theorem findCandidate?_capture {index cut : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {candidate : Candidate Input saved carried result extra}
    (found : findCandidate? index cut origins code = some candidate) :
    findCaptured? index cut origins code = some candidate :=
  Option.eq_some_of_filter_eq_some found

/-- The one-save checker returns exactly the same handoff for prior
successful saved-dependent checks. -/
theorem prepareOn?_of_saved_capture {intermediate : Output Input carried result} {origins : List Nat}
    {index : Nat} {candidate : Candidate Input intermediate.1 carried result}
    (located : origins.idxOf? consumerOrigin = some index)
    (found : findCandidate? index 0 savedOrigins (intermediate.2.block .header) = some candidate)
    (checked : checkConsumer intermediate.2 candidate = true) :
    prepareOn? intermediate origins consumerOrigin = some ⟨intermediate, origins, index, candidate⟩ := by
  simp [prepareOn?, located, findCandidate?_capture found, checked]

/-- The captured operands evaluate the current typed binding in a header activation. -/
theorem findCaptured?_value {index cut : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {candidate : Candidate Input saved carried result extra}
    (found : findCaptured? index cut origins code = some candidate)
    (env : Env Γ) (inputs : Env ((extra ++ [saved]) ++ Input)) (agree : CapturesAgree origins env inputs) :
    valueAt? index code env = some ⟨candidate.width, evalOp candidate.op (candidate.inputs.eval inputs)⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.findCaptured?_value
    found env inputs agree

theorem findCandidate?_value {index cut : Nat}
    {origins : Origins (saved :: Input) Γ} {code : Block TargetOp (Label saved carried result) Γ [result]}
    {candidate : Candidate Input saved carried result}
    (found : findCandidate? index cut origins code = some candidate)
    (env : Env Γ) (inputs : Env (saved :: Input)) (agree : CapturesAgree origins env inputs) :
    valueAt? index code env = some ⟨candidate.width, evalOp candidate.op (candidate.inputs.eval inputs)⟩ :=
  findCaptured?_value (findCandidate?_capture found) env inputs agree

/-- Immutable captures have definition sites at entry cut zero and exact
operand values for every saved-prefix environment. -/
theorem findCaptured?_immutable {index cut : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {candidate : Candidate Input saved carried result extra} {inputs : Operands Input candidate.args}
    (found : findCaptured? index cut origins code = some candidate) (immutable : candidate.immutableInputs? = some inputs) :
    (∀ operand ∈ candidate.operands, operand = ⟨none, 0⟩) ∧
    ∀ (input : Env Input) (values : Env (extra ++ [saved])),
      candidate.inputs.eval (values.append input) = inputs.eval input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.findCaptured?_immutable found immutable

theorem findCaptured?_earliest_eq_zero {index cursor : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]} {inputs : Operands Input candidate.args}
    (found : findCaptured? index cursor origins code = some candidate) (immutable : candidate.immutableInputs? = some inputs) :
    candidate.earliestCut = 0 := by
  apply Nat.eq_zero_of_le_zero (Candidate.earliestCut_le_iff.mpr fun operand member => ?_)
  rw [(findCaptured?_immutable found immutable).1 operand member]
  exact Nat.le_refl 0

/-- The intermediate CFG is exactly the first hoist's replay result. -/
theorem prepare?_replay_first (accepted : prepare? g first consumerOrigin = some prepared) :
    AfterReorder.replay? g first = some prepared.intermediate :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepare?_replay_first accepted

/-- Removal transports the origin table to the actual intermediate header,
and the consumer's definition and use sites admit preheader cut one. -/
theorem prepare?_placement (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ (state : State Input carried result) (firstIndex : Nat),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      state.origins[firstIndex]? = some first.hoistOrigin ∧
      prepared.origins = state.origins.eraseIdx firstIndex ∧
      prepared.origins[prepared.index]? = some consumerOrigin ∧
      prepared.origins.map (fun origin => (operations ((lower g).block .header))[origin]?) =
        (operations (prepared.intermediate.2.block .header)).map some ∧
      findCaptured? prepared.index 0 savedOrigins (prepared.intermediate.2.block .header) =
        some prepared.consumer ∧
      Legal prepared.intermediate.2 prepared.consumer.operands prepared.consumer.uses ⟨none, 1⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepare?_placement accepted

/-- Immediately after the first preheader binding, the consumer can be
evaluated from the resulting value and immutable inputs for any latch. -/
theorem prepare?_available (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      ∀ (input : Env Input) (old : BitVec carried.val),
        let saved := evalOp producer (operands.eval input)
        valueAt? prepared.index (prepared.intermediate.2.block .header) (.cons saved (.cons old input)) =
          some ⟨prepared.consumer.width, evalOp prepared.consumer.op
            (prepared.consumer.inputs.eval (.cons saved input))⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepare?_available accepted

/-- The leading preheader let computes the exact value supplied by the first
emitter on entry and feedback. The exit block is the canonical return. -/
theorem prepare?_first_routes (accepted : prepare? g first consumerOrigin = some prepared)
    (input : Env Input) :
    ∃ (source : Cfg TargetOp (SourceLabel carried result) Input [result])
      (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      prepared.intermediate.2.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      Routes source prepared.intermediate.2 input (evalOp producer (operands.eval input)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepare?_first_routes accepted input

/-- The routing invariant is based on the exact checked header sequence. -/
theorem prepare?_first_replay_routes (accepted : prepare? g first consumerOrigin = some prepared)
    (input : Env Input) :
    ∃ (state : State Input carried result)
      (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      prepared.intermediate.2.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      Routes state.cfg prepared.intermediate.2 input (evalOp producer (operands.eval input)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.prepare?_first_replay_routes accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
