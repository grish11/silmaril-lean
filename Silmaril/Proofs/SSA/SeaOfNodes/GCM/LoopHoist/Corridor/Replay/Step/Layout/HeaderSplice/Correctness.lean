module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice
open AfterReorder.Second (intermediateBlocks savedHeader targetDecEqWith)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Layout.State Input saved carried result extra} {request : Nomination} {move : Move state}

private theorem sameSites_eq {Labels : List Width → Type} [DecidableEq (Target Labels)]
    {a b : Layout.CrossBlock.HeaderSites Labels} (equal : sameSites a b = true) : a = b := by
  have point : Function.Injective (sameSites.point (Labels := Labels)) := by
    rintro ⟨_, _⟩ ⟨_, _⟩ eq
    cases eq
    rfl
  have occurrence : Function.Injective (sameSites.occurrence (Labels := Labels)) := by
    rintro (_ | ⟨_, _, _⟩) (_ | ⟨_, _, _⟩) eq
    · exact congrArg Use.ordinary (point (Sum.inl.inj eq))
    · cases eq
    · cases eq
    · cases eq
      rfl
  obtain ⟨operands, uses⟩ := of_decide_eq_true equal
  cases a
  cases b
  congr
  · exact (List.map_inj_right (f := sameSites.point) (fun _ _ eq => point eq)).mp operands
  · exact (List.map_inj_right (f := sameSites.occurrence) (fun _ _ eq => occurrence eq)).mp uses

theorem emit?_spec (accepted : emit? state request = some move) :
    move.request = request ∧ Layout.CrossBlock.keep? state request.origin = some move.binding ∧
    (move.insertion + 1 = move.binding.index ∨ move.binding.index + 1 = move.insertion) ∧
    Legal state.cfg move.binding.sites.operands move.binding.sites.uses move.cut ∧
    Header.Typed.swapAt? (min move.binding.index move.insertion) (state.cfg.block .header) = some move.header ∧
    Layout.CrossBlock.findSites? move.next move.insertion 0 (Saved.origins (extra ++ [saved]))
      (move.next.cfg.block .header) = some move.binding.sites := by
  let _ := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
  cases supported : Layout.Discovery.supported? state with
  | false => simp [emit?, supported] at accepted
  | true =>
    simp only [emit?, supported, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at accepted
    obtain ⟨kept, found, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    let insertion := Header.afterRemoval kept.index request.cut
    by_cases adjacent : insertion + 1 = kept.index ∨ kept.index + 1 = insertion
    · simp only [← show insertion = Header.afterRemoval kept.index request.cut from rfl, ite_eq_left adjacent] at accepted
      by_cases valid : GCM.Dominance.Placement.checkCut state.cfg intermediateBlocks kept.sites.operands
          kept.sites.uses ⟨savedHeader, request.cut⟩ = true
      · simp only [ite_eq_left valid] at accepted
        obtain ⟨header, swapped, accepted⟩ := Option.bind_eq_some_iff.mp accepted
        obtain ⟨sites, scanned, accepted⟩ := Option.bind_eq_some_iff.mp accepted
        by_cases same : sameSites kept.sites sites = true
        · simp only [ite_eq_left same, Option.some.injEq] at accepted
          subst move
          exact ⟨rfl, found, adjacent, (GCM.Dominance.Placement.checkCut_iff.mp valid).2,
            swapped, (sameSites_eq same).symm ▸ scanned⟩
        · simp [same] at accepted
      · simp [valid] at accepted
    · simp [show Header.afterRemoval kept.index request.cut = insertion from rfl, adjacent] at accepted

theorem emit?_order (accepted : emit? state request = some move) :
    ∃ (prefixOps : List Header.Earlier.Operation) (left right : Header.Earlier.Operation)
      (suffixOps : List Header.Earlier.Operation),
      prefixOps.length = min move.binding.index move.insertion ∧
      Header.Earlier.operations (state.cfg.block .header) = prefixOps ++ (left :: right :: suffixOps) ∧
      Header.Earlier.operations (move.next.cfg.block .header) = prefixOps ++ (right :: left :: suffixOps) :=
  Header.Earlier.swapAt_typed_order (emit?_spec accepted).2.2.2.2.1

theorem emit?_refuses {binding : Layout.CrossBlock.Kept (Label saved carried result extra)}
    (found : Layout.CrossBlock.keep? state request.origin = some binding)
    (illegal : ¬ Legal state.cfg binding.sites.operands binding.sites.uses ⟨savedHeader, request.cut⟩) :
    emit? state request = none := by
  cases accepted : emit? state request with
  | none => rfl
  | some move =>
    obtain ⟨rfl, resolved, _, legal, _⟩ := emit?_spec accepted
    cases Option.some.inj (found.symm.trans resolved)
    exact False.elim (illegal legal)

theorem next_invariant (valid : Layout.Invariant state) : Layout.Invariant move.next :=
  ⟨valid.scopeSize, valid.prefixAgreement, valid.targets, valid.entry⟩

theorem emit?_frames (accepted : emit? state request = some move) (input : Env Input) :
    move.next.cfg.entry = state.cfg.entry ∧
    move.next.cfg.block .exit = state.cfg.block .exit ∧
    ∀ frame : Frame (Label saved carried result extra),
      (move.next.cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        (state.cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) := by
  refine ⟨rfl, rfl, ?_⟩
  rintro ⟨label, args⟩
  cases label with
  | header => exact Header.Typed.swapAt?_eval (emit?_spec accepted).2.2.2.2.1 (args.append input)
  | exit => rfl

theorem emit?_edgePackets (accepted : emit? state request = some move)
    (env : Env (((extra ++ [saved]) ++ [carried]) ++ Input)) :
    (move.next.cfg.block .header).eval evalOp Header.Typed.edgePackets env =
      (state.cfg.block .header).eval evalOp Header.Typed.edgePackets env :=
  Header.Typed.swapAt?_edgePackets (emit?_spec accepted).2.2.2.2.1 env

theorem emit?_routes {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])}
    (accepted : emit? state request = some move) (prior : RoutesWith base state.cfg input values) :
    RoutesWith base move.next.cfg input values := by
  refine ⟨prior.entry, fun frame => ?_⟩
  exact ((emit?_frames accepted input).2.2 (carryFrameWith values frame)).trans (prior.block frame)

theorem emit?_run_eq (accepted : emit? state request = some move) (input : Env Input) (fuel : Nat) :
    move.next.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input :=
  let ⟨entry, _, block⟩ := emit?_frames accepted input
  Header.Typed.run_eq_of_frames input entry block fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem emit?_denotePart (accepted : emit? state request = some move) (input : Env Input) :
    (Cfg.embed move.next.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, emit?_run_eq accepted]

variable {ranked : Ranked state} {headerCut : Nat}

theorem rank?_spec (accepted : rank? state request headerCut = some ranked) :
    Layout.CrossBlock.analyze? state request = some ranked.crossBlock ∧
    ranked.header = emit? state ⟨request.origin, headerCut⟩ := by
  obtain ⟨crossBlock, checked, same⟩ := Option.bind_eq_some_iff.mp accepted
  cases same
  exact ⟨checked, rfl⟩

theorem selection_depth (ranked : Ranked state) :
    ranked.crossBlock.control.depth ranked.selection.1.block =
      ranked.crossBlock.control.depth ranked.crossBlock.point.block := by
  cases chosen : ranked.laterHeader? with
  | none => simp [Ranked.selection, chosen]
  | some move =>
    cases outside : ranked.crossBlock.selectedMove?.isSome with
    | false =>
      simp [Ranked.selection, chosen, Layout.CrossBlock.Analysis.point, outside, Move.cut,
        Layout.CrossBlock.Kept.point]
    | true => simp [Ranked.laterHeader?, outside] at chosen

theorem selected_minDepth (ranked : Ranked state) :
    ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth savedHeader ∧
    (ranked.crossBlock.preheader.isSome →
      ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth none) :=
  ⟨(selection_depth ranked).le.trans (Layout.CrossBlock.selected_minDepth ranked.crossBlock).1,
    fun admitted => (selection_depth ranked).le.trans
      ((Layout.CrossBlock.selected_minDepth ranked.crossBlock).2.1 admitted)⟩

theorem laterHeader?_iff (move : Move state) :
    ranked.laterHeader? = some move ↔
      ranked.crossBlock.selectedMove?.isSome = false ∧ ranked.header = some move ∧
        ranked.crossBlock.kept.point.cut < move.cut.cut := by
  cases outside : ranked.crossBlock.selectedMove?.isSome <;> simp [Ranked.laterHeader?, outside]

theorem rank?_candidate (accepted : rank? state request headerCut = some ranked)
    (candidate : ranked.header = some move) :
    emit? state ⟨request.origin, headerCut⟩ = some move ∧ move.binding = ranked.crossBlock.kept := by
  obtain ⟨outside, inside⟩ := rank?_spec accepted
  have emitted := inside.symm.trans candidate
  have moved := (emit?_spec emitted).2.1
  have kept := (Layout.CrossBlock.analyze?_spec outside).2.2.1
  exact ⟨emitted, Option.some.inj (moved.symm.trans kept)⟩

theorem rank?_run_eq {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state request headerCut = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) (fuel : Nat) :
    ranked.selection.2.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input := by
  obtain ⟨control, candidate⟩ := rank?_spec accepted
  cases chosen : ranked.laterHeader? with
  | none =>
    unfold Ranked.selection
    rw [chosen]
    exact Layout.CrossBlock.analyze?_run_eq control valid prior matched fuel
  | some moved =>
    have emitted := candidate.symm.trans ((laterHeader?_iff moved).mp chosen).2.1
    unfold Ranked.selection
    rw [chosen]
    exact emit?_run_eq emitted input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem rank?_denotePart {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state request headerCut = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    (Cfg.embed ranked.selection.2.2.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, rank?_run_eq accepted valid prior matched]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice
