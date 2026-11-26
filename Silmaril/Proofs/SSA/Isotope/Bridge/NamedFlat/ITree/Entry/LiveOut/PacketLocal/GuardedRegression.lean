module

import Mathlib.Tactic.FinCases
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Thms

/-! # A named request changes its loop packet before taking an ordered exit -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Tests

open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree vis vis_bind iterate_fixpoint HasTrace out_ret hasTrace_vis_exchange_iff)
open Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet pack)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Table ReplyEnumeration ConfigurationEnumeration)

private inductive Op where | poll | flip | literal (bit : Bool)
  deriving DecidableEq

private inductive Reg : Type 1 where
  | seed | arg | alt | again | rest | left | tail | right | impossible
  deriving DecidableEq

private inductive Label : Type 1 where
  | loop | left | right | first | second
  deriving DecidableEq

private abbrev Bit := Recognize.Bit
private abbrev Packets := Recognize.Packets
private abbrev Replies := Packets

attribute [local instance] Recognize.requestTypes

private abbrev nativeSig := Recognize.signature Op

private abbrev SortName := ULift.{1} Empty
private abbrev bit : Ty SortName := .coprod .unit .unit
private instance : HasTy Op (Ty SortName) :=
  ⟨(fun
    | .poll | .flip => bit
    | .literal _ => .unit), fun
    | .poll => LambdaSSA.Region.packedExitType [bit, .unit, .unit]
    | .flip | .literal _ => bit⟩
private instance : HasEff Op Bool := ⟨fun
  | .poll | .flip => true
  | .literal _ => false⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName := { Instr := Op }
private instance : DecidableEq signature.Instr := inferInstanceAs (DecidableEq Op)

private def labels : Fin 5 ≃ Label where
  toFun i := if i = 0 then .loop else if i = 1 then .left else if i = 2 then .right
    else if i = 3 then .first else .second
  invFun
    | .loop => 0
    | .left => 1
    | .right => 2
    | .first => 3
    | .second => 4
  left_inv := by decide +kernel
  right_inv := by intro label; cases label <;> rfl

private def ports : Interface SortName Reg Label := Recognize.interface .seed labels

private def fields (_ : Label) : List (Reg × Ty SortName) := []
private def loopReg (alternate : Bool) : Reg := if alternate then .alt else .arg

/-- The final arm is required by the named sum syntax. Its empty payload
can never be supplied by the shared typed request. -/
private def source (alternate : Bool) (reroute prequery : Bool := false) : CFG Reg Label signature.Instr :=
  let param := loopReg alternate
  let poll : CFG.Body Reg Label signature.Instr := .term (.case (.app .poll (.var param))
    .again (.br .loop (.var .again))
    .rest (.case (.val (.var .rest))
      .left (.br (if reroute then .right else .left) (.var .left))
      .tail (.case (.val (.var .tail))
        .right (.br .right (.var .right)) .impossible (.br .right .unit))))
  let body := if prequery then .let1 param (.app .flip (.var param)) poll else poll
  ⟨.term (.br .loop (.var .seed)),
    [(.loop, ⟨param, body⟩),
     (.left, ⟨.arg, .term (.br .first .unit)⟩),
     (.right, ⟨.arg, .term (.br .second .unit)⟩)]⟩

private def arguments (i : Fin 3) : Ty SortName := if i = 0 then bit else .unit
private def admitNamed (alternate : Bool) (reroute prequery : Bool := false) :=
  PacketLocal.admit (P := signature) ports fields (source alternate reroute prequery) arguments

private def admitted (alternate : Bool) (reroute prequery : Bool := false) :
    Admission signature ports fields (source alternate reroute prequery) :=
  (admitNamed alternate reroute prequery).get
    (by cases alternate <;> cases reroute <;> cases prequery <;> decide +kernel)

private def leftBit : Syntax.Payload Bit := ⟨.inl .unit, .inl .unit⟩
private def rightBit : Syntax.Payload Bit := ⟨.inr .unit, .inr .unit⟩
private def unitPacket : Syntax.Payload (.unit : Syntax.Ty) := ⟨.unit, .unit⟩

private inductive Event : Type → Type where
  | poll (arg : Bool) : Event (Packet Replies)

private abbrev Runtime := ULift.{1} Unit

universe u

private def isRight {A : Type u} : Value A → Bool
  | .inr _ => true
  | _ => false

private def query : Query nativeSig Event :=
  fun _ p => vis (.poll (isRight p.val)) fun reply => pure ⟨reply⟩

private def raw : Primitive Event signature.Instr Runtime :=
  fun
    | .poll, x => vis (.poll (isRight x)) fun reply => pure (Recognize.replyValue ULift.up reply)
    | .flip, x => pure (if isRight x then .inl .unit else .inr .unit)
    | .literal b, _ => pure (Recognize.bitValue b)

private def input (x : Syntax.Payload Bit) : Reg × Nat → Value Runtime :=
  fun reg => if reg = (.seed, 0) then Recognize.encodeValue ULift.up x.val else .unit

-- The compiled entry really sends the extra unit field. The native entry
-- forwards its caller directly, so this is an encoding equation.
example : (admitted false).versioned.table.code.entry =
    .br ⟨0, by decide +kernel⟩ (.pair (.bv ⟨0, by decide⟩) .unit) := rfl

-- The named compiler installs a leading product decoder before the query.
example : (admitted false).versioned.table.code.block ⟨0, by decide +kernel⟩ =
    .let₂ (.bv 0) (.case (.op .poll (.bv 1))
      (.br ⟨0, by decide +kernel⟩ (.pair (.bv 0) .unit))
      (.case (.bv 0)
        (.br ⟨1, by decide +kernel⟩ (.pair (.bv 0) .unit))
        (.case (.bv 0)
          (.br ⟨2, by decide +kernel⟩ (.pair (.bv 0) .unit))
          (.br ⟨2, by decide +kernel⟩ (.pair .unit .unit))))) := rfl

private theorem agrees : Recognize.QueryAgreement (P := signature) .poll ULift.up query raw := by
  intro argument
  have key : isRight (Recognize.encodeValue ULift.up argument.val : Value Runtime) = isRight argument.val := by
    cases argument.val <;> rfl
  simp only [raw, query, key, vis_bind, pure_bind]

private def adapter (alternate : Bool) (caller : Syntax.Payload Bit) (reroute prequery : Bool := false) :=
  Recognize.recognizeAdapter (seed := Reg.seed) (names := labels) (admitted alternate reroute prequery)
    .poll ULift.up query raw (input caller) agrees caller rfl

private theorem recognized (alternate reroute : Bool) :
    (Recognize.recognize (seed := Reg.seed) (names := labels) (admitted alternate reroute) .poll).isSome = true := by
  cases alternate <;> cases reroute <;> decide +kernel

private def checkedAdapter (alternate : Bool) (caller : Syntax.Payload Bit) (reroute : Bool := false) :=
  (adapter alternate caller reroute).get (by
    unfold adapter Recognize.recognizeAdapter
    rw [Option.isSome_map]
    exact recognized alternate reroute)

private abbrev nativeRoutes := (checkedAdapter false leftBit).1
private abbrev native := Recognize.guardedTable Op.poll nativeRoutes
private abbrev rerouted := Recognize.guardedTable Op.poll (checkedAdapter false leftBit true).1

private def firstUnitDestination (table : Table nativeSig Packets) : Option Nat :=
  match table.row 0 with
  | .request _ _ next _ => some (next 1).val
  | .exit .. => none

-- The guarded heads use the destinations extracted from the compiled row.
example : firstUnitDestination native = some 1 ∧ firstUnitDestination rerouted = some 2 :=
  ⟨rfl, rfl⟩

example : native ≠ rerouted := fun eq => (by decide : some (1 : Nat) ≠ some 2)
  (congrArg firstUnitDestination eq)

-- A separate primitive before the poll changes the query bit. The named
-- compiler accepts it, but this recognizer requires the exact request row.
example : (admitNamed false false true).isSome = true := by decide +kernel

example : (adapter false leftBit false true).isNone = true := by decide +kernel

private def packets : List (Packet Packets) :=
  [⟨0, leftBit⟩, ⟨0, rightBit⟩, ⟨1, unitPacket⟩, ⟨2, unitPacket⟩]

private theorem packets_complete (packet : Packet Packets) : packet ∈ packets := by
  obtain ⟨i, value, typed⟩ := packet
  fin_cases i
  · cases typed with
    | inl typed => cases typed; exact List.Mem.head _
    | inr typed => cases typed; exact List.Mem.tail _ (List.Mem.head _)
  · cases typed
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  · cases typed
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

private def replies : ReplyEnumeration nativeSig := ⟨fun _ => packets, fun _ => packets_complete⟩
private def inventory : ConfigurationEnumeration Packets := ⟨packets, packets_complete⟩
private def diagonal : List (Packet Packets × Packet Packets) := packets.map fun p => (p, p)

private noncomputable def observation (alternate : Bool) (reroute : Bool := false) :=
  LiveOut.observeRaw raw ports.exits (fun k => (fields k).map Prod.fst) (source alternate reroute)
    (fun reg => input leftBit (reg, 0))

example : observation false = observation true :=
  observe_eq_of_checkProduct ((checkedAdapter false leftBit).2) ((checkedAdapter true leftBit).2)
    replies diagonal (by decide +kernel) (fun _ => rfl)

example : (match native.searchProduct native leftBit leftBit replies inventory inventory with
    | .accepted _ => true
    | .mismatch .. => false) = true := by decide +kernel

example : observation false = observation true := by
  obtain ⟨pairs, accepted⟩ := (native.searchProduct_accepts_iff native leftBit leftBit replies inventory
    inventory).mpr ⟨diagonal, by decide +kernel⟩
  exact observe_eq_of_searchProduct ((checkedAdapter false leftBit).2) ((checkedAdapter true leftBit).2)
    replies inventory inventory pairs accepted (fun _ => rfl)

private theorem observe_routes (reroute : Bool) : observation false reroute =
    iter (step (Recognize.guardedTable Op.poll (checkedAdapter false leftBit reroute).1)
      leftBit query (unitExit (α := Runtime))) (atBlock ⟨0, leftBit⟩) :=
  (checkedAdapter false leftBit reroute).2.observe_eq

-- The derived adapter computes the actual rerouted named runner.
example : observation false true =
    iter (step rerouted leftBit query (unitExit (α := Runtime))) (atBlock ⟨0, leftBit⟩) :=
  observe_routes true

-- Shared reply tag one reaches different ordinary ordered exits.
example : (match native.searchProduct rerouted leftBit leftBit replies inventory inventory with
    | .accepted _ => none
    | .mismatch pair path => some (pair.1.1.val, pair.2.1.val, path.map fun edge => edge.1.2.1.val)) =
    some (1, 2, [0, 1]) := by decide +kernel

private def runStep := step native leftBit query (unitExit (α := Runtime))

private theorem native_reply (reply : Packet Packets) :
    (⟨nativeRoutes.destination reply.1,
      cast (congrArg Syntax.Payload (nativeRoutes.packet reply.1).symm) reply.2⟩ : Packet Packets) = reply := by
  obtain ⟨i, payload⟩ := reply
  fin_cases i <;> rfl

private theorem runsPoll (x : Syntax.Payload Bit) :
    iter runStep (atBlock ⟨0, x⟩) =
      vis (.poll (isRight x.val)) (fun reply => iter runStep (atBlock reply)) := by
  rw [congrFun (iterate_fixpoint runStep) (atBlock ⟨0, x⟩)]
  change ((query .poll x >>= fun p => pure (Sum.inr (atBlock (R := Packets)
    ⟨nativeRoutes.destination p.down.1,
      cast (congrArg Syntax.Payload (nativeRoutes.packet p.down.1).symm) p.down.2⟩)
    : Transfer Runtime ⊕ Cursor Packets)) >>= _) = _
  simp only [native_reply, query, vis_bind, pure_bind, Sum.elim_inr]

private theorem runsRight :
    iter runStep (atBlock ⟨2, unitPacket⟩) = pure (unitExit 1) := by
  rw [congrFun (iterate_fixpoint runStep) (atBlock ⟨2, unitPacket⟩)]
  change ((pure (.inr (atExit (R := Packets) 1)) : Tree Event (Transfer Runtime ⊕ Cursor Packets)) >>= _) = _
  rw [pure_bind]
  change iter runStep (atExit 1) = _
  rw [congrFun (iterate_fixpoint runStep) (atExit 1)]
  change ((pure (.inl (unitExit 1)) : Tree Event (Transfer Runtime ⊕ Cursor Packets)) >>= _) = _
  rw [pure_bind]
  rfl

-- Reply tag zero changes the loop argument from left to right. Reply tag
-- two then leaves at the second ordered exit.
example : HasTrace (observation false)
    (.exchange (.poll false) ⟨0, rightBit⟩
      (.exchange (.poll true) ⟨2, unitPacket⟩ (.result (unitExit 1)))) := by
  rw [observe_routes false]
  change HasTrace (iter runStep (atBlock ⟨0, leftBit⟩)) _
  rw [runsPoll]
  apply (hasTrace_vis_exchange_iff _ _ _ _).mpr
  rw [runsPoll]
  apply (hasTrace_vis_exchange_iff _ _ _ _).mpr
  rw [runsRight]
  exact out_ret _

section FixedCarrier

open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag resultBehaviour result_order)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)

private def checkedReadback (reroute : Bool) :=
  (Recognize.recognize (seed := Reg.seed) (names := labels) (admitted false reroute) .poll).get
    (recognized false reroute)

private abbrev inferred (reroute : Bool) := Recognize.guardedTable Op.poll (checkedReadback reroute).routes

private theorem nativeValid (reroute : Bool) : (inferred reroute).checkNative (inferred reroute).native = true := by
  cases reroute <;> decide +kernel

private def states : StateInventory 2 := ⟨List.finRange 2, List.mem_finRange⟩

/-- Change the packet and machine state before returning reply tag one. -/
private def rerouteInterpreter : Syntax.Primitives Op 2 :=
  InterpreterScript.interpret [
    InterpreterScript.Row.success (S := nativeSig) ⟨.poll, leftBit, 0⟩ ⟨0, rightBit⟩ 1,
    InterpreterScript.Row.success (S := nativeSig) ⟨.poll, rightBit, 1⟩ ⟨1, unitPacket⟩ 1]

private noncomputable def named (reroute : Bool) (prim : Syntax.Primitives Op 2)
    (selected : Tag → Bool := fun _ => false) :=
  FixedCarrier.observeNamed (source false reroute) labels (fun reg => input leftBit (reg, 0)) prim 0 selected

private theorem named_classifies (reroute : Bool) (prim : Syntax.Primitives Op 2)
    (selected : Tag → Bool := fun _ => false) :
    named reroute prim selected =
      resultBehaviour ((FixedCarrier.withSelectedExits Op.poll (checkedReadback reroute).routes selected).runFinite
        leftBit prim inventory states ⟨0, leftBit⟩ 0) :=
  FixedCarrier.observeNamed_runFinite (checkedReadback reroute) leftBit _ rfl prim inventory states 0 selected

example : named false rerouteInterpreter = resultBehaviour (.ret 0 1) := by
  rw [named_classifies]
  rfl

example : named true rerouteInterpreter = resultBehaviour (.ret 1 1) := by
  rw [named_classifies]
  rfl

private theorem rerouteWitness : ¬ named false rerouteInterpreter ≤ named true rerouteInterpreter := by
  rw [named_classifies false, named_classifies true, result_order]
  change ¬ (Result.ret (0 : Fin 2) (1 : Fin 2)).refines (.ret 1 1)
  decide

-- Both exact native readbacks pass. The verdict uses a typed, total
-- deterministic interpreter at the original named endpoints.
example : (inferred false).checkAllInterpreters? (inferred true)
    (inferred false).native (inferred true).native leftBit leftBit replies inventory inventory states = some false := by
  apply (FixedCarrier.rejection_iff (checkedReadback false) (checkedReadback true) leftBit (fun reg => input leftBit (reg, 0)) rfl
    replies inventory states _ _ (nativeValid false) (nativeValid true)).mpr
  exact ⟨rerouteInterpreter, 0, rerouteWitness⟩

private def selectedExit (i : Tag) : Bool := i == 1

private abbrev decorated (reroute : Bool) :=
  FixedCarrier.withSelectedExits Op.poll (checkedReadback reroute).routes selectedExit

private theorem originalSelected : named false rerouteInterpreter selectedExit = resultBehaviour (.ret 0 1) := by
  rw [named_classifies false _ selectedExit]
  rfl

private theorem reroutedSelected : named true rerouteInterpreter selectedExit = ⊤ := by
  rw [named_classifies true _ selectedExit]
  rfl

private def selectedPairs : List (Packet Packets × Packet Packets) :=
  (⟨1, unitPacket⟩, ⟨2, unitPacket⟩) :: diagonal

private theorem selectedProduct :
    (decorated false).checkProduct (decorated true) leftBit leftBit replies selectedPairs = true := by
  decide +kernel

-- Both checks reuse the original native representatives and their readbacks.
example : (decorated false).checkAllInterpreters? (decorated true)
    (inferred false).native (inferred true).native leftBit leftBit replies inventory inventory states = some true := by
  apply (FixedCarrier.acceptance_iff (checkedReadback false) (checkedReadback true) leftBit
    (fun reg => input leftBit (reg, 0)) rfl replies inventory states _ _
    (nativeValid false) (nativeValid true) selectedExit selectedExit).mpr
  intro prim s
  rw [FixedCarrier.observeNamed_native (checkedReadback false) leftBit _ rfl prim inventory states _
      (nativeValid false) s selectedExit,
    FixedCarrier.observeNamed_native (checkedReadback true) leftBit _ rfl prim inventory states _
      (nativeValid true) s selectedExit]
  exact (decorated false).checkProduct_sound (decorated true) _ _ (nativeValid false) (nativeValid true)
    leftBit leftBit replies selectedPairs selectedProduct prim s

example : (decorated true).checkAllInterpreters? (decorated false)
    (inferred true).native (inferred false).native leftBit leftBit replies inventory inventory states = some false := by
  apply (FixedCarrier.rejection_iff (checkedReadback true) (checkedReadback false) leftBit
    (fun reg => input leftBit (reg, 0)) rfl replies inventory states _ _
    (nativeValid true) (nativeValid false) selectedExit selectedExit).mpr
  refine ⟨rerouteInterpreter, 0, ?_⟩
  change ¬ named true rerouteInterpreter selectedExit ≤ named false rerouteInterpreter selectedExit
  rw [reroutedSelected, originalSelected]
  change ¬ resultBehaviour (.ub : Result 2 2) ≤ resultBehaviour (.ret 0 1)
  rw [result_order]
  decide

example : named false (fun _ _ _ => .fault 1) selectedExit = resultBehaviour (.fault 1) := by
  rw [named_classifies false _ selectedExit]
  rfl

private def repeating : Syntax.Primitives Op 2 :=
  fun _ arg s => .ret (pack (L := Packets) ⟨0, arg⟩) (if s = 0 then 1 else 0)

private theorem repeating_cycle :
    (decorated false).runFinite leftBit repeating inventory states ⟨0, leftBit⟩ 0 = .diverge := by
  decide +kernel

-- Every request resumes the original loop with the alternating machine state.
example : named false repeating selectedExit = resultBehaviour .diverge := by
  rw [named_classifies false repeating selectedExit, repeating_cycle]

namespace LiveBitRegression

open FixedCarrier (resultWithPayload)

private def exitBits (value : Bool) (i : Tag) : Bool := if i = 0 then value else false
private def literalOps (value : Bool) (i : Tag) : Op := .literal (exitBits value i)

private def liveSource (value : Bool) : CFG Reg Label signature.Instr :=
  let g := source false
  { g with blocks := g.blocks.map fun (k, row) =>
      match k with
      | .left => (k, { row with body := .let1 .left (.app (literalOps value 0) .unit) row.body })
      | .right => (k, { row with body := .let1 .left (.app (literalOps value 1) .unit) row.body })
      | _ => (k, row) }

private def liveAdmission? (value : Bool) :=
  PacketLocal.admit (P := signature) ports (FixedCarrier.LiveBit.fields Reg.left) (liveSource value) arguments

private def liveAdmitted (value : Bool) :
    Admission signature ports (FixedCarrier.LiveBit.fields Reg.left) (liveSource value) :=
  (liveAdmission? value).get (by cases value <;> decide +kernel)

private def liveChecked? (value : Bool) :=
  Recognize.recognize (seed := Reg.seed) (names := labels) (liveAdmitted value) .poll
    (fun i => some (literalOps value i))

-- The other program's assignment is rejected by exact lexical readback.
example : (Recognize.recognize (seed := Reg.seed) (names := labels) (liveAdmitted true) .poll
    (fun i => some (literalOps false i))).isNone = true := by decide +kernel

private def liveChecked (value : Bool) :=
  (liveChecked? value).get (by cases value <;> decide +kernel)

private abbrev liveControl (value : Bool) := Recognize.guardedTable Op.poll (liveChecked value).routes

private theorem liveNativeValid (value : Bool) : (liveControl value).checkNative (inferred false).native = true := by
  cases value <;> decide +kernel

private def literals : Op → Option Bool
  | .literal b => some b
  | _ => none

private theorem literalsAgree (value : Bool) (i : Tag) :
    literals (literalOps value i) = some (exitBits value i) := rfl

private def callerStore (r : Reg) := input leftBit (r, 0)

private noncomputable def observed (value : Bool) (selected : Tag → Bool := fun _ => false) :=
  FixedCarrier.LiveBit.observeNamed (liveSource value) labels .left callerStore literals rerouteInterpreter 0 selected

private theorem classified (value : Bool) (selected : Tag → Bool) :
    observed value selected = resultWithPayload (fun i => Recognize.exitPayload (some (exitBits value i)))
      ((FixedCarrier.withSelectedExits Op.poll (liveChecked value).routes selected).runFinite
        leftBit rerouteInterpreter inventory states ⟨0, leftBit⟩ 0) :=
  FixedCarrier.LiveBit.observeNamed_runFinite (liveChecked value) leftBit callerStore rfl literals (literalsAgree value)
    rerouteInterpreter inventory states 0 selected

private theorem liveReturned (value : Bool) :
    observed value = resultWithPayload (fun i => Recognize.exitPayload (some (exitBits value i))) (.ret 0 1) := by
  cases value <;> rw [classified] <;> rfl

example (value : Bool) :
    LambdaSSA.UB.Overlay.Shape.denote (FixedCarrier.LiveBit.nativeEndpoint (inferred false).native (exitBits value) (fun _ => false))
      (Syntax.model rerouteInterpreter ((liveControl value).bindings leftBit)) 0 =
        resultWithPayload (fun i => Recognize.exitPayload (some (exitBits value i))) (.ret 0 1) :=
  (FixedCarrier.LiveBit.observeNamed_native (liveChecked value) leftBit callerStore rfl literals
    (literalsAgree value) rerouteInterpreter inventory states _ (liveNativeValid value) 0 _).symm.trans
    (liveReturned value)

private theorem differingLiveOut : ¬ observed false ≤ observed true := by
  rw [liveReturned false, liveReturned true, ← FixedCarrier.LiveBit.compare_iff]
  decide +kernel

-- Both controls return unit at the same position in state one under this script.
-- The negative verdict is caused by the projected assignment.
example : FixedCarrier.LiveBit.check? .poll .poll (liveChecked false).routes (liveChecked true).routes
    (inferred false).native (inferred false).native (exitBits false) (exitBits true)
    (fun _ => false) (fun _ => false) leftBit replies inventory states = some false := by
  apply (FixedCarrier.LiveBit.rejection_iff (liveChecked false) (liveChecked true) leftBit callerStore rfl
    literals (literalsAgree false) (literalsAgree true) replies inventory states _ _
    (liveNativeValid false) (liveNativeValid true) _ _).mpr
  exact ⟨rerouteInterpreter, 0, differingLiveOut⟩

-- Selecting that ordered exit erases the whole payload on each endpoint.
example (value : Bool) : observed value (fun i => i == 0) = ⊤ := by
  cases value <;> rw [classified] <;> rfl

end LiveBitRegression

end FixedCarrier

namespace DynamicLiveOut

open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open FixedCarrier.LiveBit (PayloadType payloadExpr)

private abbrev Incoming : List Syntax.Ty := [Bit, Bit, .unit]
private abbrev Outputs := Payload.Exits PayloadType

private def targets (tag : Fin 3) : Fin 3 := if tag = 0 then 1 else 2

private abbrev control (selected : Tag → Bool) : Table nativeSig Incoming where
  entry := 0
  row := Fin.cases (motive := fun i : Fin 3 => Row nativeSig Incoming [Incoming.get i, Bit])
    (.request .poll (.var 0) targets (by intro i; fin_cases i <;> rfl))
    (fun _ => .exit 0)
  selected := selected

private abbrev endpoint (fixed : Bool) (selected : Tag → Bool) : Endpoint nativeSig Incoming PayloadType where
  control := control selected
  output := Fin.cases (motive := fun i : Fin 3 => Syntax.Expr [Incoming.get i, Bit] PayloadType)
    (payloadExpr false)
    (Fin.cases (motive := fun i : Fin 2 => Syntax.Expr [Incoming.get i.succ, Bit] PayloadType)
      (if fixed then payloadExpr false else .pair .unit (.pair (.var 0) .unit))
      (fun _ => payloadExpr false))

private def outgoing (tag : Tag) (bit : Bool) : Packet Outputs :=
  ⟨tag, cast (congrArg Syntax.Payload (Payload.exit_type tag).symm)
    ((payloadExpr bit).eval Syntax.emptyBindings)⟩

private def payloadBit (value : Value Unit) : Bool :=
  match value with
  | .pair .unit (.pair (.inr .unit) .unit) => true
  | _ => false

private def codes : Fin 4 ≃ Packet Outputs where
  toFun i := outgoing (if i.val < 2 then 0 else 1) (i.val % 2 == 1)
  invFun p := ⟨p.1.val * 2 + (if payloadBit p.2.val then 1 else 0), by
    have bounded := p.1.isLt
    change p.1.val < 2 at bounded
    split <;> omega⟩
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by
    rintro ⟨tag, value, typed⟩
    fin_cases tag <;>
      cases typed with
      | pair old field =>
        cases old
        cases field with
        | pair bit tail =>
          cases tail
          cases bit with
          | inl bit => cases bit; rfl
          | inr bit => cases bit; rfl

private def packets : List (Packet Incoming) :=
  [⟨0, leftBit⟩, ⟨0, rightBit⟩, ⟨1, leftBit⟩, ⟨1, rightBit⟩, ⟨2, unitPacket⟩]

private def configs : ConfigurationEnumeration Incoming := ⟨packets, by
  rintro ⟨i, value, typed⟩
  fin_cases i
  · cases typed with
    | inl h => cases h; exact List.Mem.head _
    | inr h => cases h; exact List.Mem.tail _ (List.Mem.head _)
  · cases typed with
    | inl h => cases h; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    | inr h => cases h; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  · cases typed
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩

private def script (bit : Bool) : Syntax.Primitives Op 2 :=
  InterpreterScript.interpret [
    InterpreterScript.Row.success (S := nativeSig) ⟨.poll, leftBit, 0⟩
      ⟨0, if bit then rightBit else leftBit⟩ 1]

private def noSelection : Tag → Bool := fun _ => false
private abbrev dynamic := endpoint false noSelection
private abbrev fixed := endpoint true noSelection
private abbrev marked := endpoint false (fun i => i == 0)

private theorem valid (fixed : Bool) (selected : Tag → Bool) :
    (endpoint fixed selected).checkNative (endpoint fixed selected).native = true := by
  have exactCheck : (endpoint fixed noSelection).checkNative (endpoint fixed noSelection).native = true := by
    cases fixed <;> decide +kernel
  exact exactCheck

private noncomputable def observed (fixed : Bool) (selected : Tag → Bool) (prim : Syntax.Primitives Op 2) :=
  LambdaSSA.UB.Overlay.Shape.denote
    (CFG.Dependent.Native.withExitUB (endpoint fixed selected).native selected)
    (Syntax.model prim ((control selected).bindings leftBit)) 0

private theorem observesDynamic (bit : Bool) : observed false noSelection (script bit) =
    WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 bit).2.val (1 : Fin 2)} := by
  unfold observed
  rw [dynamic.observe_entry codes _ (valid false noSelection) leftBit _ configs states]
  cases bit <;> rfl

private theorem observesFixed : observed true noSelection (script true) =
    WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 false).2.val (1 : Fin 2)} := by
  unfold observed
  rw [fixed.observe_entry codes _ (valid true noSelection) leftBit _ configs states]
  rfl

-- A single ordered exit exposes either payload under the two shared scripts.
example : observed false noSelection (script false) = WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 false).2.val (1 : Fin 2)} :=
  observesDynamic false

example : observed false noSelection (script true) = WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 true).2.val (1 : Fin 2)} :=
  observesDynamic true

example : observed false (fun i => i == 0) (script true) = ⊤ := by
  unfold observed
  rw [marked.observe_entry codes _ (valid false _) leftBit _ configs states]
  rfl

private theorem witness : ¬ observed false noSelection (script true) ≤ observed true noSelection (script true) := by
  rw [observesDynamic true, observesFixed]
  simp [WithTop.coe_le_coe, outgoing, payloadExpr, Syntax.Expr.eval]
  intro eq; cases eq

-- The fixed projection is a different typed native readback.
example : dynamic.checkNative fixed.native = false := by decide +kernel

private def namedSource (fixed : Bool) : CFG Reg Label signature.Instr :=
  let finish : CFG.Body Reg Label signature.Instr := .term (.br .first .unit)
  let fixedFinish := .let1 .left (.app (.literal false) .unit) finish
  ⟨.term (.br .loop (.var .seed)),
    [(.loop, ⟨.arg, .term (.case (.app .poll (.var .arg))
      .again (.br .left (.var .again))
      .rest (.case (.val (.var .rest))
        .left (.br .right (.var .left))
        .tail (.case (.val (.var .tail))
          .right (.br .right (.var .right)) .impossible (.br .right .unit))))⟩),
     (.left, ⟨.left, if fixed then fixedFinish else finish⟩),
     (.right, ⟨.arg, fixedFinish⟩)]⟩

private def argumentTypes (i : Fin 3) : Ty SortName := if i = 2 then .unit else bit

private def namedAdmission (fixed : Bool) :
    Admission signature ports (FixedCarrier.LiveBit.fields Reg.left) (namedSource fixed) :=
  (PacketLocal.admit (P := signature) ports (FixedCarrier.LiveBit.fields Reg.left)
    (namedSource fixed) argumentTypes).get (by cases fixed <;> decide +kernel)

-- The attached dynamic exit reads the version of the block parameter,
-- and the fixed exit reads the new assignment rather than that parameter.
example : (namedAdmission false).versioned.table.code.block ⟨1, by decide +kernel⟩ =
    .let₂ (.bv 0) (.br ⟨3, by decide +kernel⟩ (.pair .unit (.pair (.bv 1) .unit))) := rfl

example : (namedAdmission true).versioned.table.code.block ⟨1, by decide +kernel⟩ =
    .let₂ (.bv 0) (.let₁ (.op (.literal false) .unit) (.br ⟨3, by decide +kernel⟩ (.pair .unit (.pair (.bv 0) .unit)))) := rfl

example (fixed : Bool) : (namedAdmission fixed).versioned.table.code.entry =
    .br ⟨0, by cases fixed <;> decide +kernel⟩
      (.pair (.bv ⟨0, by decide⟩) .unit) := by cases fixed <;> rfl

example (fixed : Bool) : (namedAdmission fixed).versioned.table.code.block
    ⟨0, by cases fixed <;> decide +kernel⟩ =
    .let₂ (.bv 0) (.case (.op .poll (.bv 1))
      (.br ⟨1, by cases fixed <;> decide +kernel⟩ (.pair (.bv 0) .unit))
      (.case (.bv 0)
        (.br ⟨2, by cases fixed <;> decide +kernel⟩ (.pair (.bv 0) .unit))
        (.case (.bv 0)
          (.br ⟨2, by cases fixed <;> decide +kernel⟩ (.pair (.bv 0) .unit))
          (.br ⟨2, by cases fixed <;> decide +kernel⟩ (.pair .unit .unit))))) := by
  cases fixed <;> rfl

example (fixed : Bool) : (namedAdmission fixed).versioned.table.code.block
    ⟨2, by cases fixed <;> decide +kernel⟩ =
    .let₂ (.bv 0) (.let₁ (.op (.literal false) .unit)
      (.br ⟨3, by cases fixed <;> decide +kernel⟩ (.pair .unit (.pair (.bv 0) .unit)))) := by
  cases fixed <;> rfl

private def literalValues : Op → Option Bool
  | .literal bit => some bit
  | _ => none

private abbrev instr := FixedCarrier.LiveBit.rawWithLiterals literalValues
private abbrev m := treeModel instr
private def seedStore (r : Reg) := input leftBit (r, 0)
private def emit (value : Value Runtime) : Transfer Runtime :=
  LambdaSSA.FiniteCFG.packedTreeOutput (0, .pair .unit (.pair value .unit))

private def low : Value Runtime := .inl .unit

private def returned (fixed : Bool) (reply : Packet Replies) :=
  emit (if fixed || reply.1 != 0 then low else Recognize.encodeValue ULift.up reply.2.val)

private def walk (fixed : Bool) (p : Packet Incoming) : FixedCarrier.RunTree Op :=
  Fin.cases (motive := fun i : Fin 3 => Syntax.Payload (Incoming.get i) → FixedCarrier.RunTree Op)
    (fun x => vis (FixedCarrier.Request.call .poll x) (fun reply => Silmaril.Elgot.ITree.ret (returned fixed reply)))
    (Fin.cases (motive := fun i : Fin 2 => Syntax.Payload (Incoming.get i.succ) → FixedCarrier.RunTree Op)
      (fun x => Silmaril.Elgot.ITree.ret (emit (if fixed then low else Recognize.encodeValue ULift.up x.val)))
      (fun _ _ => Silmaril.Elgot.ITree.ret (emit low))) p.1 p.2

private theorem walk_roots (fixed : Bool) (selected : Tag → Bool) :
    FixedCarrier.RootAgrees (endpoint fixed selected) leftBit (walk fixed) := by
  rintro ⟨i, value⟩
  fin_cases i
  · change vis (FixedCarrier.Request.call Op.poll value) (fun reply => pure (returned fixed reply)) =
      vis (FixedCarrier.Request.call Op.poll value) _
    congr 1
    funext reply
    rcases reply with ⟨tag, payload⟩
    fin_cases tag <;> cases fixed <;> rfl
  · cases fixed <;> rfl
  · rfl

private theorem payload_decodes (p : Packet Outputs) :
    FixedCarrier.LiveBit.decode (FixedCarrier.packedReturn p) = some (p.1, p.2.val) := by
  obtain ⟨i, rfl⟩ := codes.surjective p
  fin_cases i <;> rfl

private abbrev NamedState := CFG.Cyclic.Transfer Reg Label (Value Runtime)
private abbrev namedStep (fixed : Bool) := CFG.Cyclic.step m (namedSource fixed).blocks

private def packFinal (out : NamedState) : Transfer Runtime :=
  LambdaSSA.FiniteCFG.packedTreeOutput
    (treeExitNumber ports.exits (obs (CFG.Cyclic.LiveOut.project m (fun _ => [.left]) out)))

private theorem finish_named (fixed fallback : Bool) (σ : Reg → Value Runtime) (v : Value Runtime) :
    (iter (namedStep fixed) (if fallback then .right else .left, v, σ) >>= fun out => pure (packFinal out)) =
      pure (emit (if fixed || fallback then low else v)) := by
  let final : NamedState := (.first, .unit,
    if fallback then upd (upd σ .arg v) .left low
    else if fixed then upd (upd σ .left v) .left low else upd σ .left v)
  have step : namedStep fixed (if fallback then .right else .left, v, σ) = pure (.inr final) := by
    cases fallback <;> cases fixed <;>
      first
      | rfl
      | change (pure low >>= fun x => pure (Sum.inr (Label.first, Value.unit, upd _ Reg.left x) : NamedState ⊕ NamedState)) = _
        rw [pure_bind]
        rfl
  have miss : namedStep fixed final = pure (.inl final) := by cases fixed <;> rfl
  rw [congrFun (iterate_fixpoint (namedStep fixed)), step, pure_bind]
  change (iter (namedStep fixed) final >>= _) = _
  rw [congrFun (iterate_fixpoint (namedStep fixed)), miss, pure_bind, Sum.elim_inl, pure_bind]
  cases fixed <;> cases fallback <;> rfl

private theorem named_tree (fixed : Bool) :
    LiveOut.observeRaw instr ports.exits (fun _ => [.left]) (namedSource fixed) seedStore =
      walk fixed ⟨0, leftBit⟩ := by
  unfold LiveOut.observeRaw
  change (iter (namedStep fixed) (.loop, .inl .unit, seedStore) >>= fun out => pure (packFinal out)) = _
  have head : namedStep fixed (.loop, .inl .unit, seedStore) =
      vis (FixedCarrier.Request.call Op.poll leftBit) (fun reply =>
        let value := Recognize.encodeValue ULift.up reply.2.val
        pure (.inr (if reply.1 = 0 then .left else .right, value,
          if reply.1 = 0 then upd (upd seedStore .arg (.inl .unit)) .again value
          else if reply.1 = 1 then upd (upd (upd seedStore .arg (.inl .unit)) .rest (.inl value)) .left value
          else upd (upd (upd (upd seedStore .arg (.inl .unit)) .rest (.inr (.inl value)))
            .tail (.inl value)) .right value))) := by
    simp only [namedStep, CFG.Cyclic.step, namedSource, List.lookup, beq_self_eq_true]
    dsimp
    simp only [CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval, treeModel, upd,
      ite_true, FixedCarrier.LiveBit.rawWithLiterals, FixedCarrier.raw, vis_bind, pure_bind, bind_assoc]
    congr 1
    funext reply
    rcases reply with ⟨tag, value⟩
    fin_cases tag <;> let v : Value Runtime := Recognize.encodeValue ULift.up value.val
    · have eq : Recognize.replyValue ULift.up (⟨0, value⟩ : Packet Replies) = .inl v := rfl
      simp [eq, pure_bind]
      rfl
    · have eq : Recognize.replyValue ULift.up (⟨1, value⟩ : Packet Replies) = .inr (.inl v) := rfl
      simp [eq, pure_bind]
      rfl
    · have eq : Recognize.replyValue ULift.up (⟨2, value⟩ : Packet Replies) = .inr (.inr (.inl v)) := rfl
      simp [eq, pure_bind]
      rfl
  rw [congrFun (iterate_fixpoint (namedStep fixed)), head, vis_bind, vis_bind]
  change vis (FixedCarrier.Request.call Op.poll leftBit) _ =
    vis (FixedCarrier.Request.call Op.poll leftBit) _
  congr 1
  funext reply
  rcases reply with ⟨tag, value⟩
  fin_cases tag
  · simp only [pure_bind, Sum.elim_inr]
    exact finish_named fixed false _ _
  · simp only [pure_bind, Sum.elim_inr]
    exact finish_named fixed true _ _
  · simp only [pure_bind, Sum.elim_inr]
    exact finish_named fixed true _ _

private noncomputable def namedObserved (fixed : Bool) (selected : Tag → Bool)
    (prim : Syntax.Primitives Op 2) (s : Fin 2 := 0) :=
  FixedCarrier.LiveBit.observeNamed (namedSource fixed) labels .left seedStore literalValues prim s selected

private theorem named_observes (fixed : Bool) (selected : Tag → Bool)
    (prim : Syntax.Primitives Op 2) (s : Fin 2) :
    namedObserved fixed selected prim s =
      LambdaSSA.UB.Overlay.Shape.denote
        (CFG.Dependent.Native.withExitUB (endpoint fixed selected).native selected)
        (Syntax.model prim ((control selected).bindings leftBit)) s := by
  unfold namedObserved FixedCarrier.LiveBit.observeNamed
  change FixedCarrier.decorate prim selected
    (FixedCarrier.observe prim (LiveOut.observeRaw instr ports.exits (fun _ => [.left])
      (namedSource fixed) seedStore) s FixedCarrier.LiveBit.decode) PayloadType = _
  rw [named_tree]
  exact FixedCarrier.observe_roots_native (endpoint fixed selected) codes leftBit _
    (valid fixed selected) prim configs states (walk fixed) (walk_roots fixed selected) _
    payload_decodes s

example (bit : Bool) : namedObserved false noSelection (script bit) =
    WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 bit).2.val (1 : Fin 2)} :=
  (named_observes false noSelection (script bit) 0).trans (observesDynamic bit)

example : namedObserved true noSelection (script true) =
    WithTop.some {Outcome.ret (0 : Tag) (outgoing 0 false).2.val (1 : Fin 2)} :=
  (named_observes true noSelection (script true) 0).trans observesFixed

private theorem named_witness :
    ¬ namedObserved false noSelection (script true) ≤ namedObserved true noSelection (script true) := by
  rw [named_observes false noSelection, named_observes true noSelection]
  exact witness

example : dynamic.checkAllInterpreters? fixed dynamic.native fixed.native codes leftBit leftBit
    replies configs configs states = some false := by
  apply (dynamic.rejection_iff fixed _ _ codes leftBit leftBit replies configs configs states
    (valid false noSelection) (valid true noSelection)).mpr
  refine ⟨script true, 0, ?_⟩
  rw [← named_observes false noSelection, ← named_observes true noSelection]
  exact named_witness

example (fixed bit : Bool) : namedObserved fixed (fun i => i == 0) (script bit) = ⊤ := by
  rw [named_observes fixed, (endpoint fixed _).observe_entry codes _ (valid fixed _) leftBit _ configs states]
  cases fixed <;> cases bit <;> rfl

end DynamicLiveOut

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Tests
