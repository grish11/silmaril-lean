module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Defs
import Mathlib.Tactic.FinCases
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Thms

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier

open Silmaril
open Silmaril.Isotope
open Silmaril.Elgot (iter)
open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (Tree vis ret out out_vis out_ret vis_bind iterate_fixpoint)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Recognize (Bit Packets guardedTable)
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape (denote)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet unpack)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits Tag resultBehaviour)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (withExitUB denote_exitContinuation)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (Head Table ConfigurationEnumeration ReplyEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier (encode rows)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)

attribute [local instance] Recognize.requestTypes

variable {Φ : Type} {states : Nat}

theorem query_agrees (op : Φ) :
    ∀ arg : Syntax.Payload Bit,
      raw op (Recognize.encodeValue ULift.up arg.val) =
        (query op arg >>= fun p => pure (Recognize.replyValue ULift.up p.down)) := by
  rintro ⟨value, typed⟩
  cases typed with
  | inl typed => cases typed; simp only [raw, query, Recognize.encodeValue, vis_bind, pure_bind]; rfl
  | inr typed => cases typed; simp only [raw, query, Recognize.encodeValue, vis_bind, pure_bind]; rfl

private theorem exitTag_unit (i : Fin 2) : exitTag (unitExit (α := Runtime) i) = some i := by
  fin_cases i <;> rfl

private theorem run_head (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry)) (result : Tag → Nat × Value Runtime) (p : Packet Packets) :
    iter (m := Tree (Request Φ)) (step g caller query result) (atBlock p) =
      match g.head caller p with
      | .exit i _ => ret (result i)
      | .request f arg next =>
        vis (.call f arg) (fun reply =>
          iter (step g caller query result) (atBlock (next reply.1 reply.2))) := by
  rw [congrFun (iterate_fixpoint (step g caller query result)) (atBlock p)]
  change (headStep query (g.head caller p) >>= _) = _
  cases g.head caller p with
  | exit i selected =>
    simp only [headStep, pure_bind, Sum.elim_inr]
    rw [congrFun (iterate_fixpoint (step g caller query result)) (atExit i)]
    simp only [step, atExit, pure_bind, Sum.elim_inl]
    rfl
  | request f arg next =>
    simp only [headStep, query, vis_bind, pure_bind, Sum.elim_inr]

private noncomputable def carrier (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry)) (result : Tag → Nat × Value Runtime)
    (payload : Tag → Value Unit) (configs : ConfigurationEnumeration Packets) (stores : StateInventory states) :
    PositionalCarrier Loop Exits (RunTree Φ) (Fin states) (configs.invocations stores).length 2 states where
  invocation code :=
    let input := (configs.invocations stores).get code
    (0, .atom (iter (m := Tree (Request Φ)) (step g caller query result) (atBlock input.1)), input.2)
  result := ⟨fun i => (i, Recognize.encodeValue (fun _ => Silmaril.Elgot.ITree.diverge) (payload i)), fun _ _ eq => congrArg Prod.fst eq⟩
  final := ⟨id, fun _ _ eq => eq⟩

private theorem get_encode (configs : ConfigurationEnumeration Packets) (stores : StateInventory states)
    (p : Packet Packets × Fin states) : (configs.invocations stores).get (encode configs stores p) = p :=
  List.getElem_idxOf _

private theorem step_row (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry)) (prim : Syntax.Primitives Φ states)
    (result : Tag → Nat × Value Runtime) (decode : ExitDecoder) (payload : Tag → Value Unit)
    (decodes : ∀ i, decode (result i) = some (i, payload i))
    (configs : ConfigurationEnumeration Packets) (stores : StateInventory states)
    (code : Fin (configs.invocations stores).length) :
    feedback prim decode (invocationPoint (carrier g caller result payload configs stores).invocation code) =
      (rows g caller prim configs stores code).routed (carrier g caller result payload configs stores) := by
  let i := (configs.invocations stores).get code
  change treeStep prim
    (iter (m := Tree (Request Φ)) (step g caller query result) (atBlock i.1)) i.2 decode = _
  rw [run_head, rows]
  dsimp only
  cases h : g.head caller i.1 with
  | exit tag selected =>
    simp [Head.execute, treeStep, decodes, Row.routed, carrier, terminal]
    rfl
  | request f arg next =>
    simp only [Head.execute, treeStep, out_vis, Part.some_dom, ↓reduceDIte, Part.get_some]
    cases hp : prim f arg i.2 with
    | ret reply t =>
      simp only [Row.routed, carrier]
      rw [get_encode]
      rfl
    | fault t => rfl
    | diverge => rfl

theorem lower_lift {Φ : Type} (p : Value Unit) :
    Recognize.encodeValue (fun _ => ()) (Recognize.encodeValue
      (fun _ => (Silmaril.Elgot.ITree.diverge : RunTree Φ)) p) = p := by
  induction p with
  | atom a => cases a; rfl
  | unit => rfl
  | pair _ _ l r => simp [Recognize.encodeValue, l, r]
  | inl _ ih | inr _ ih => simp [Recognize.encodeValue, ih]

private theorem project_result (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry)) (result : Tag → Nat × Value Runtime)
    (payload : Tag → Value Unit) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (r : Result 2 states) :
    (r.routed (carrier g caller result payload configs stores)).map (Set.image project) =
      resultWithPayload payload r := by
  cases r <;> simp [Result.routed, carrier, project, resultWithPayload]
  exact ⟨rfl, lower_lift _⟩

private theorem decorate_result (g : Table (Recognize.signature Φ) Packets)
    (prim : Syntax.Primitives Φ states) (payload : Tag → Value Unit) (r : Result 2 states)
    (exitType : Syntax.Ty) :
    decorate prim g.selected (resultWithPayload payload r) exitType = resultWithPayload payload (g.markExit r) := by
  simp only [decorate, denote_exitContinuation]
  cases r with
  | ret i t =>
    cases h : g.selected i <;>
      simp [Table.markExit, h, resultWithPayload, Behaviour.bind, Behaviour.possible]
    ext outcome
    cases outcome <;> simp [Outcome.bind, h]
  | fault t =>
    simp [Table.markExit, resultWithPayload, Behaviour.bind, Behaviour.possible]
    ext outcome
    cases outcome <;> simp [Outcome.bind]
  | diverge =>
    simp [Table.markExit, resultWithPayload, Behaviour.bind, Behaviour.possible]
    ext outcome
    cases outcome <;> simp [Outcome.bind]
  | ub => simp [Table.markExit, resultWithPayload]

theorem step_selected (op : Φ) (routes : Recognize.Routes) (selected : Tag → Bool)
    (caller : Syntax.Payload Bit) (result : Tag → Nat × Value Runtime) :
    step (withSelectedExits op routes selected) caller query result =
      step (guardedTable op routes) caller query result := by
  funext cursor
  obtain ⟨c⟩ := cursor
  cases c with
  | inl i => rfl
  | inr packet =>
    change headStep query ((withSelectedExits op routes selected).head caller packet) =
      headStep query ((guardedTable op routes).head caller packet)
    unfold Table.head
    cases (guardedTable op routes).row packet.1 <;> rfl

theorem observe_decoded_runFinite (g : Table (Recognize.signature Φ) Packets)
    (caller : Syntax.Payload (Packets.get g.entry)) (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration Packets) (stores : StateInventory states)
    (result : Tag → Nat × Value Runtime) (decode : ExitDecoder) (payload : Tag → Value Unit)
    (decodes : ∀ i, decode (result i) = some (i, payload i))
    (p : Packet Packets) (s : Fin states) (exitType : Syntax.Ty := .unit) :
    decorate prim g.selected (FixedCarrier.observe prim
      (iter (m := Tree (Request Φ)) (step g caller query result) (atBlock p)) s decode) exitType =
      resultWithPayload payload (g.runFinite caller prim configs stores p s) := by
  have h := classify_routed (f := feedback prim decode) (carrier g caller result payload configs stores)
    (rows g caller prim configs stores) (encode configs stores (p, s)) (step_row g caller prim result decode payload decodes configs stores)
  have atStart : invocationPoint (carrier g caller result payload configs stores).invocation
      (encode configs stores (p, s)) =
      .block 0 (.atom (iter (m := Tree (Request Φ)) (step g caller query result) (atBlock p))) s := by
    simp only [invocationPoint, carrier, get_encode]
  rw [atStart] at h
  unfold FixedCarrier.observe Table.runFinite
  rw [h, project_result]
  exact decorate_result g prim payload _ exitType

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {seed : V} {names : Fin 5 ≃ K}
  {source target : CFG V K P.Instr}
  {a : Admission P (Recognize.interface seed names) (fun _ => []) source}
  {b : Admission P (Recognize.interface seed names) (fun _ => []) target}
  {op op' : P.Instr}

theorem observeNamed_runFinite (checked : Recognize.Checked a op) (caller : Syntax.Payload Bit)
    (input : V → Value Runtime) (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (s : Fin states) (selected : Tag → Bool := fun _ => false) :
    observeNamed source names input prim s selected =
      resultBehaviour ((withSelectedExits op checked.routes selected).runFinite caller prim configs stores ⟨0, caller⟩ s) := by
  let c := checked.corresponds ULift.up query raw (fun reg => input reg.1) (query_agrees op) caller value
  have classified := observe_decoded_runFinite (withSelectedExits op checked.routes selected)
    caller prim configs stores unitExit unitDecoder (fun _ => .unit)
    (fun i => by simp [unitDecoder, exitTag_unit]) ⟨0, caller⟩ s
  rw [step_selected] at classified
  exact (congrArg (fun tree => decorate prim selected (FixedCarrier.observe prim tree s)) c.observe_eq).trans classified

theorem observeNamed_native [DecidableEq P.Instr] (checked : Recognize.Checked a op)
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native : CFG.Dependent.Native.Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op checked.routes).checkNative native = true) (s : Fin states)
    (selected : Tag → Bool := fun _ => false) :
    observeNamed source names input prim s selected =
      Shape.denote (withExitUB native selected)
        (Syntax.model prim ((guardedTable op checked.routes).bindings caller)) s := by
  let g := withSelectedExits op checked.routes selected
  calc
    _ = resultBehaviour (g.runFinite caller prim configs stores ⟨0, caller⟩ s) :=
      observeNamed_runFinite checked caller input value prim configs stores s selected
    _ = g.observeAt caller prim ⟨0, caller⟩ s := (g.observe_runFinite caller prim configs stores _ s).symm
    _ = _ := (g.observe_entry native readback caller prim s).symm

theorem acceptance_iff [DecidableEq P.Instr] (left : Recognize.Checked a op) (right : Recognize.Checked b op')
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (replies : ReplyEnumeration (Recognize.signature P.Instr)) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native native' : CFG.Dependent.Native.Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op left.routes).checkNative native = true)
    (readback' : (guardedTable op' right.routes).checkNative native' = true)
    (selected selected' : Tag → Bool := fun _ => false) :
    (withSelectedExits op left.routes selected).checkAllInterpreters?
        (withSelectedExits op' right.routes selected') native native'
        caller caller replies configs configs stores = some true ↔
      ∀ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        observeNamed source names input prim s selected ≤ observeNamed target names input prim s selected' := by
  have leftRead : (withSelectedExits op left.routes selected).checkNative native = true := readback
  have rightRead : (withSelectedExits op' right.routes selected').checkNative native' = true := readback'
  rw [Table.checkAllInterpreters?_accepts_iff, and_iff_right leftRead, and_iff_right rightRead]
  exact forall_congr' fun prim => forall_congr' fun s => by
    rw [observeNamed_native left caller input value prim configs stores native readback s selected,
      observeNamed_native right caller input value prim configs stores native' readback' s selected']
    rfl

theorem rejection_iff [DecidableEq P.Instr] (left : Recognize.Checked a op) (right : Recognize.Checked b op')
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (value : input seed = Recognize.encodeValue ULift.up caller.val)
    (replies : ReplyEnumeration (Recognize.signature P.Instr)) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native native' : CFG.Dependent.Native.Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op left.routes).checkNative native = true)
    (readback' : (guardedTable op' right.routes).checkNative native' = true)
    (selected selected' : Tag → Bool := fun _ => false) :
    (withSelectedExits op left.routes selected).checkAllInterpreters?
        (withSelectedExits op' right.routes selected') native native'
        caller caller replies configs configs stores = some false ↔
      ∃ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        ¬ observeNamed source names input prim s selected ≤ observeNamed target names input prim s selected' := by
  classical
  have accepted := acceptance_iff left right caller input value replies configs stores native native' readback readback' selected selected'
  have leftRead : (withSelectedExits op left.routes selected).checkNative native = true := readback
  have rightRead : (withSelectedExits op' right.routes selected').checkNative native' = true := readback'
  simp only [Table.checkAllInterpreters?, leftRead, rightRead, Bool.and_self, ↓reduceIte,
    Option.some.injEq] at accepted ⊢
  simp only [Bool.eq_false_iff, ne_eq, accepted, not_forall]

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
