module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Defs
import Mathlib.Data.List.InsertIdx
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier (operations)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence (State)
open Loop.MLIR.CF (Program TargetOp evalOp lower)
open Dominance.Placement (checkCut)

variable {Input Γ Δ extra : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {first : AfterReorder.Plan} {consumerOrigin : Nat} {prepared : Prepared Input carried result}
variable {candidate : Candidate Input saved carried result extra}
variable {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}

local instance : DecidableEq (Target (Label saved carried result extra)) := targetDecEqWith

theorem earliestCut_le_iff {cut : Nat} :
    candidate.earliestCut ≤ cut ↔ ∀ operand ∈ candidate.operands, operand.cut ≤ cut := by
  unfold Candidate.earliestCut
  generalize listEq : candidate.operands.map Point.cut = cuts
  have same : (∀ c ∈ cuts, c ≤ cut) ↔ ∀ operand ∈ candidate.operands, operand.cut ≤ cut := by
    rw [← listEq]
    simp
  rw [← same]
  cases maximum : cuts.max? with
  | none => simp [List.max?_eq_none_iff.mp maximum]
  | some max => exact List.max?_le_iff maximum

theorem checkPrefixCut_legal {cut : Nat} (accepted : checkPrefixCut cfg candidate cut = true) :
    Legal cfg candidate.operands candidate.uses ⟨none, cut⟩ :=
  (Dominance.Placement.checkCut_iff.mp (Bool.and_eq_true_iff.mp accepted).2).2

private theorem savedOrigins_agree (value : BitVec saved.val) (old : BitVec carried.val)
    (input : Env Input) : CapturesAgree savedOrigins (.cons value (.cons old input)) (.cons value input) :=
  Saved.origins_agree (.cons value .nil) old input

theorem findCaptured?_value {index cut : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {candidate : Candidate Input saved carried result extra}
    (found : findCaptured? index cut origins code = some candidate)
    (env : Env Γ) (inputs : Env ((extra ++ [saved]) ++ Input)) (agree : CapturesAgree origins env inputs) :
    valueAt? index code env = some ⟨candidate.width, evalOp candidate.op (candidate.inputs.eval inputs)⟩ := by
  induction code generalizing index cut with
  | terminator => simp [findCaptured?] at found
  | letOp op operands rest ih =>
    cases index with
    | zero =>
      cases capture : captureOrigins? origins operands with
      | none => simp [findCaptured?, capture] at found
      | some captured =>
        simp [findCaptured?, capture] at found
        subst candidate
        simp only [valueAt?, evalCaptureOrigins origins operands capture env inputs agree]
    | succ index =>
      apply ih found (.cons (evalOp op (operands.eval env)) env)
      intro _ ref captured fromOrigin
      cases ref with
      | here => cases fromOrigin
      | there ref => exact agree ref captured fromOrigin

theorem findCaptured?_sites {index cut : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {candidate : Candidate Input saved carried result extra}
    (found : findCaptured? index cut origins code = some candidate) :
    candidate.operands = prefixSites candidate.inputs := by
  induction code generalizing index cut with
  | terminator => simp [findCaptured?] at found
  | letOp op operands rest ih =>
    cases index with
    | zero =>
      cases capture : captureOrigins? origins operands with
      | none => simp [findCaptured?, capture] at found
      | some inputs =>
        simp only [findCaptured?, capture] at found
        cases found
        rfl
    | succ index => exact ih found

private theorem prefixSites_bounds {args : List Width} (inputs : Operands ((extra ++ [saved]) ++ Input) args)
    (operand : Point (Label saved carried result extra)) (member : operand ∈ prefixSites inputs) :
    operand.block = none ∧ operand.cut ≤ (extra ++ [saved]).length := by
  induction inputs with
  | nil => simp [prefixSites] at member
  | cons ref tail ih =>
    simp only [prefixSites, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨rfl, Nat.sub_le _ _⟩
    · exact ih member

theorem findCaptured?_operandCut_end {index cursor : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    (found : findCaptured? index cursor origins code = some candidate) :
    candidate.operandCut? (extra ++ [saved]).length = true := by
  apply decide_eq_true
  refine ⟨earliestCut_le_iff.mpr (fun operand member => ?_), Nat.le_refl _⟩
  rw [findCaptured?_sites found] at member
  exact (prefixSites_bounds _ operand member).2

theorem findCaptured?_checkConsumer_eq {index cursor : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    (found : findCaptured? index cursor origins code = some candidate) :
    checkConsumer cfg candidate =
      checkCut cfg intermediateBlocks candidate.operands candidate.uses ⟨none, (extra ++ [saved]).length⟩ := by
  simp only [checkConsumer, checkPrefixCut, findCaptured?_operandCut_end found, Bool.true_and]

private theorem prefix_wrap_bindings {Δ : List Width} (leading : Saved.Prefix Input Δ)
    (tail : Block TargetOp (Label saved carried result extra) Δ [result]) :
    (shape.ofBlock (leading.wrap tail)).bindings + Input.length =
      (shape.ofBlock tail).bindings + Δ.length := by
  induction leading with
  | nil => rfl
  | snoc prior op operands ih =>
    rw [Saved.Prefix.wrap, ih]
    simp only [shape.ofBlock, List.length_cons]
    omega

theorem findCaptured?_operandCut_iff {index cut : Nat}
    {leading : Saved.Prefix Input ((extra ++ [saved]) ++ Input)}
    {tail : Block TargetOp (Label saved carried result extra) ((extra ++ [saved]) ++ Input) [result]}
    (split : Saved.splitPrefix? cfg.entry (extra ++ [saved]) = some (leading, tail))
    (found : findCaptured? index 0 (Saved.origins (extra ++ [saved])) (cfg.block .header) = some candidate) :
    candidate.operandCut? cut = true ↔ cut ≤ (extra ++ [saved]).length ∧
      (Point.mk none cut).Valid cfg ∧
      ∀ operand ∈ candidate.operands, operand.Valid cfg ∧ operand.AvailableAt cfg ⟨none, cut⟩ := by
  have fits : (extra ++ [saved]).length ≤ (shape cfg none).bindings := by
    have lengths := prefix_wrap_bindings leading tail
    rw [Saved.splitPrefix?_wrap split, List.length_append] at lengths
    change (extra ++ [saved]).length ≤ (shape.ofBlock cfg.entry).bindings
    omega
  have entryReachable : Reachable cfg none := ⟨_, .entry⟩
  have entryDominates : Dominates cfg none none := by
    intro past path
    cases path
    simp
  have bounds : ∀ operand ∈ candidate.operands, operand.block = none ∧ operand.cut ≤ (extra ++ [saved]).length := by
    rw [findCaptured?_sites found]
    exact prefixSites_bounds _
  rw [Candidate.operandCut?, decide_eq_true_eq, earliestCut_le_iff]
  constructor
  · rintro ⟨ordered, within⟩
    refine ⟨within, ⟨entryReachable, within.trans fits⟩, fun operand member => ?_⟩
    obtain ⟨block, bound⟩ := bounds operand member
    cases operand with
    | mk blockId defCut =>
      cases block
      exact ⟨⟨entryReachable, bound.trans fits⟩, ⟨entryDominates, fun _ => ordered _ member⟩⟩
  · rintro ⟨within, _, available⟩
    exact ⟨fun operand member => (available operand member).2.local_order (bounds operand member).1, within⟩

private theorem immutable_sites {args : List Width} (operands : Operands ((extra ++ [saved]) ++ Input) args)
    {captured : Operands Input args}
    (found : captureOrigins? (Saved.immutableOrigins (extra ++ [saved])) operands = some captured) :
    ∀ operand ∈ prefixSites (carried := carried) (result := result) operands, operand = ⟨none, 0⟩ := by
  induction operands with
  | nil => simp [prefixSites]
  | cons ref tail ih =>
    cases origin : Saved.immutableOrigins (extra ++ [saved]) ref with
    | inr unavailable => simp [captureOrigins?, origin] at found
    | inl input =>
      simp only [captureOrigins?, origin, Option.map_eq_some_iff] at found
      obtain ⟨remaining, matched, _⟩ := found
      intro operand member
      simp only [prefixSites, List.mem_cons] at member
      rcases member with rfl | later
      · rw [Saved.immutableOrigins_cut ref origin]
      · exact ih matched operand later

theorem findCaptured?_immutable {index cut : Nat}
    {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {candidate : Candidate Input saved carried result extra} {inputs : Operands Input candidate.args}
    (found : findCaptured? index cut origins code = some candidate) (immutable : candidate.immutableInputs? = some inputs) :
    (∀ operand ∈ candidate.operands, operand = ⟨none, 0⟩) ∧
    ∀ (input : Env Input) (values : Env (extra ++ [saved])),
      candidate.inputs.eval (values.append input) = inputs.eval input := by
  refine ⟨?_, fun input values => evalCaptureOrigins _ _ immutable _ _
    (Saved.immutableOrigins_agree values input)⟩
  rw [findCaptured?_sites found]
  exact immutable_sites candidate.inputs immutable

private theorem routeCode_operations (code : Block TargetOp (SourceLabel carried result) Γ [result])
    (rename : Rename Γ Δ) (kept : Operands Δ [saved]) :
    operations (routeCodeWith (saved := saved) (extra := []) rename kept code) = operations code := by
  induction code generalizing Δ with
  | terminator => rfl
  | letOp _ _ _ ih => simp only [routeCodeWith, operations, ih]

private theorem rewrite_operations {index cut : Nat} {origins : Origins Input Γ}
    {code : Block TargetOp (SourceLabel carried result) Γ [result]}
    {binding : Binding Input Γ saved carried result}
    (found : findBinding index cut origins code = some ⟨saved, binding⟩)
    (rename : Rename Γ Δ) (keep : Var Δ saved) :
    operations (binding.rewrite rename keep) = (operations code).eraseIdx index := by
  induction code generalizing index cut Δ with
  | terminator => simp [findBinding] at found
  | letOp op operands rest ih =>
    cases index with
    | zero =>
      cases found
      exact routeCode_operations rest (replaceBinding rename keep) (.cons keep .nil)
    | succ index =>
      simp only [findBinding, Option.map_eq_some_iff] at found
      obtain ⟨⟨_, inner⟩, selected, eq⟩ := found
      cases eq
      simp only [Binding.prepend, operations, List.eraseIdx_cons_succ,
        ih selected (under rename) (.there keep)]

theorem hoistCodeWith?_operations
    {entry : Block TargetOp (SourceLabel carried result) Input [result]}
    {header : Block TargetOp (SourceLabel carried result) (carried :: Input) [result]}
    {choose : List (Point (SourceLabel carried result)) → List (Use (SourceLabel carried result)) →
      Option (Point (SourceLabel carried result))}
    {index : Nat} {cut : Point (SourceLabel carried result)} {output : Output Input carried result}
    (moved : hoistCodeWith? entry header index choose = some (cut, output)) :
    operations (output.2.block .header) = (operations header).eraseIdx index := by
  obtain ⟨binding, found, _, _, _, _, code⟩ := hoistCodeWith?_spec moved
  rw [code]
  exact rewrite_operations found Var.there .here

theorem prepareOn?_spec {intermediate : Output Input carried result} {origins : List Nat}
    (accepted : prepareOn? intermediate origins consumerOrigin = some prepared) :
    prepared.intermediate = intermediate ∧ prepared.origins = origins ∧
    prepared.origins.idxOf? consumerOrigin = some prepared.index ∧
    findCaptured? prepared.index 0 savedOrigins (prepared.intermediate.2.block .header) =
      some prepared.consumer ∧ checkConsumer prepared.intermediate.2 prepared.consumer = true := by
  obtain ⟨index, located, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨consumer, found, next⟩ := Option.bind_eq_some_iff.mp next
  cases checked : checkConsumer intermediate.2 consumer with
  | false => simp [checked] at next
  | true =>
    simp [checked] at next
    subst prepared
    exact ⟨rfl, rfl, located, found, checked⟩

private theorem prepare?_spec (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ (state : State Input carried result) (firstIndex : Nat) (cut : Point (SourceLabel carried result)),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      Header.Priority.resolve? state first.hoistOrigin = some firstIndex ∧
      hoistCodeWith? state.cfg.entry (state.cfg.block .header) firstIndex (chooseCfgCut? state.cfg) =
        some (cut, prepared.intermediate) ∧
      prepared.origins = state.origins.eraseIdx firstIndex ∧
      prepared.origins.idxOf? consumerOrigin = some prepared.index ∧
      findCaptured? prepared.index 0 savedOrigins (prepared.intermediate.2.block .header) =
        some prepared.consumer ∧
      checkConsumer prepared.intermediate.2 prepared.consumer = true := by
  obtain ⟨state, ran, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨⟨firstIndex, cut, intermediate⟩, firstMoved, next⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨resolved, moved⟩ := AfterReorder.resolveMove?_spec firstMoved
  obtain ⟨same, origins, located, found, checked⟩ := prepareOn?_spec next
  exact ⟨state, firstIndex, cut, ran, resolved, same ▸ moved, origins, located, found, checked⟩

theorem prepare?_replay_first (accepted : prepare? g first consumerOrigin = some prepared) :
    AfterReorder.replay? g first = some prepared.intermediate := by
  obtain ⟨_, _, _, ran, resolved, moved, _⟩ := prepare?_spec accepted
  simp [AfterReorder.replay?, AfterReorder.finish?, AfterReorder.resolveMove?, ran, resolved, moved]

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
      Legal prepared.intermediate.2 prepared.consumer.operands prepared.consumer.uses ⟨none, 1⟩ := by
  obtain ⟨state, firstIndex, _, ran, resolved, moved, erased, located, foundConsumer, checked⟩ := prepare?_spec accepted
  have tracked := Header.Sequence.run?_tracked (Header.Sequence.initial_tracked (lower g)) ran
  have secondAt : prepared.origins[prepared.index]? = some consumerOrigin := by
    obtain ⟨bound, eq, _⟩ := List.idxOf?_eq_some_iff.mp located
    exact List.getElem?_eq_some_iff.mpr ⟨bound, eq⟩
  have sameOrder := hoistCodeWith?_operations moved
  have aligned : prepared.origins.map (fun origin => (operations ((lower g).block .header))[origin]?) =
      (operations (prepared.intermediate.2.block .header)).map some := by
    rw [erased, ← List.eraseIdx_map, tracked.2.1, List.eraseIdx_map, sameOrder]
  exact ⟨state, firstIndex, ran, Header.Priority.resolve?_sound resolved, erased, secondAt,
    aligned, foundConsumer, checkPrefixCut_legal checked⟩

theorem prepare?_available (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      ∀ (input : Env Input) (old : BitVec carried.val),
        let saved := evalOp producer (operands.eval input)
        valueAt? prepared.index (prepared.intermediate.2.block .header) (.cons saved (.cons old input)) =
          some ⟨prepared.consumer.width, evalOp prepared.consumer.op
            (prepared.consumer.inputs.eval (.cons saved input))⟩ := by
  obtain ⟨state, _, _, _, _, moved, _, _, found, _⟩ := prepare?_spec accepted
  obtain ⟨binding, _, _, _, operands, _, code⟩ := hoistCodeWith?_spec moved
  refine ⟨binding.args, binding.op, operands, routeCode Var.there .here state.cfg.entry, ?_, ?_⟩
  · rw [code]
    rfl
  · intro input old
    exact findCaptured?_value found _ _ (savedOrigins_agree _ old input)

theorem prepare?_first_replay_routes (accepted : prepare? g first consumerOrigin = some prepared)
    (input : Env Input) :
    ∃ (state : State Input carried result)
      (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      prepared.intermediate.2.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      Routes state.cfg prepared.intermediate.2 input (evalOp producer (operands.eval input)) := by
  obtain ⟨state, _, _, ran, _, moved, _⟩ := prepare?_spec accepted
  obtain ⟨binding, found, _, _, operands, captured, code⟩ := hoistCodeWith?_spec moved
  obtain ⟨_, headerOnly, _⟩ := Header.Sequence.run?_header ran
  have exit : state.cfg.block .exit = .terminator (.ret (.cons .here .nil)) := by
    rw [headerOnly]
    rfl
  refine ⟨state, binding.args, binding.op, operands, routeCode Var.there .here state.cfg.entry,
    ran, ?_, ?_, ?_⟩
  · rw [code]
    rfl
  · rw [code]
    rfl
  · rw [code]
    exact emitHeader_routes exit binding found operands captured input

theorem prepare?_first_routes (accepted : prepare? g first consumerOrigin = some prepared)
    (input : Env Input) :
    ∃ (source : Cfg TargetOp (SourceLabel carried result) Input [result])
      (args : List Width) (producer : TargetOp args prepared.intermediate.1) (operands : Operands Input args)
      (tail : Block TargetOp (Label prepared.intermediate.1 carried result)
        (prepared.intermediate.1 :: Input) [result]),
      prepared.intermediate.2.entry = .letOp producer operands tail ∧
      prepared.intermediate.2.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      Routes source prepared.intermediate.2 input (evalOp producer (operands.eval input)) := by
  obtain ⟨state, args, producer, operands, tail, _, entry, exit, routed⟩ :=
    prepare?_first_replay_routes accepted input
  exact ⟨state.cfg, args, producer, operands, tail, entry, exit, routed⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
