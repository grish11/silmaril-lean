module

import Mathlib.Tactic.FinCases
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Recognize.Thms

/-! # A named request changes its loop packet before taking an ordered exit -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Tests

open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree vis vis_bind iterate_fixpoint HasTrace out_ret hasTrace_vis_exchange_iff)
open Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Table ReplyEnumeration ConfigurationEnumeration)

private inductive Op where | poll | flip
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
  ⟨fun _ => bit, fun
    | .poll => LambdaSSA.Region.packedExitType [bit, .unit, .unit]
    | .flip => bit⟩
private instance : HasEff Op Bool := ⟨fun _ => true⟩

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
    simpa only [adapter, Recognize.recognizeAdapter, Option.isSome_map] using recognized alternate reroute)

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

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Tests
