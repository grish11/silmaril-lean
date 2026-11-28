module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit.Defs
import Mathlib.Tactic.FinCases
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit

open Silmaril
open Silmaril.Isotope
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
  (Table ConfigurationEnumeration ReplyEnumeration)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits Tag exit_type resultBehaviour)
open Recognize (Bit Packets exitPayload exitResult guardedTable)

attribute [local instance] Recognize.requestTypes

variable {Φ : Type} {states : Nat}

private theorem decode_output (bits : Tag → Bool) (i : Tag) :
    decode (exitResult (fun j => some (bits j)) i) = some (i, exitPayload (some (bits i))) := by
  fin_cases i
  · cases h : bits 0 <;> simp [h, decode, decodeTyped, decodeBitAtExit, decodeBitAtExit.decodeBit,
      payloadExpr, Syntax.Expr.eval, exitResult, exitPayload, Recognize.bitValue,
      LambdaSSA.FiniteCFG.packedTreeOutput, LambdaSSA.Region.packedExitValue]
    all_goals rfl
  · cases h : bits 1 <;> simp [h, decode, decodeTyped, decodeBitAtExit, decodeBitAtExit.decodeBit,
      payloadExpr, Syntax.Expr.eval, exitResult, exitPayload, Recognize.bitValue,
      LambdaSSA.FiniteCFG.packedTreeOutput, LambdaSSA.Region.packedExitValue]
    all_goals rfl

private theorem eval_payload {Γ : List Syntax.Ty} (env : Syntax.Bindings Γ) (bit : Bool) :
    ((payloadExpr bit).eval env).val = exitPayload (some bit) := by cases bit <;> rfl

private theorem nativeExit_observes (prim : Syntax.Primitives Φ states) (caller : Syntax.Payload Bit)
    (bits : Tag → Bool) (i : Tag) (s : Fin states) :
    LambdaSSA.UB.Overlay.denote (.native (nativeExit bits i)) (extendModel (Syntax.model prim
      (Syntax.emptyBindings.push caller)).raw .unit) s =
      resultWithPayload (fun j => exitPayload (some (bits j))) (.ret i s) := by
  have jump_observes (j : Tag) (env : Syntax.Bindings (Exits.get j :: [Bit])) :
      LambdaSSA.UB.Overlay.denote (.native (nativeExit bits j)) (Syntax.model prim env).raw s =
        resultWithPayload (fun k => exitPayload (some (bits k))) (.ret j s) := by
    calc
      _ = WithTop.some {Outcome.ret j ((payloadExpr (bits j)).eval env).val s} :=
        CFG.observe_jump (L := LiveExits) prim env j (List.getElem_replicate j.isLt) (payloadExpr (bits j)) s
      _ = _ := by rw [eval_payload]; rfl
  let env := Syntax.emptyBindings.push caller
  let unit : Syntax.Payload (Exits.get i) := ⟨.unit, exit_type i ▸ .unit⟩
  exact (Syntax.denote_push prim env unit (.native (nativeExit bits i)) s).trans
    (jump_observes i (env.push unit))

private theorem append_payload (prim : Syntax.Primitives Φ states) (caller : Syntax.Payload Bit)
    (bits : Tag → Bool) (r : Result 2 states) :
    (resultBehaviour r).bind
      (fun i a s => LambdaSSA.UB.Overlay.denote (.native (nativeExit bits i))
        (extendModel (Syntax.model prim (Syntax.emptyBindings.push caller)).raw a) s) =
      resultWithPayload (fun i => exitPayload (some (bits i))) r := by
  cases r with
  | ret i s =>
    let k : Tag → Value Unit → Fin states → Behaviour LiveExits.length Unit (Fin states) :=
      fun j a t => LambdaSSA.UB.Overlay.denote (.native (nativeExit bits j))
        (extendModel (Syntax.model prim (Syntax.emptyBindings.push caller)).raw a) t
    change (resultBehaviour (.ret i s)).bind k = _
    have h : k i .unit s = resultWithPayload (fun j => exitPayload (some (bits j))) (.ret i s) :=
      nativeExit_observes prim caller bits i s
    simp [resultBehaviour, Behaviour.bind, Behaviour.possible, h, resultWithPayload]
    ext outcome
    cases outcome <;> simp [Outcome.bind, h, resultWithPayload]
  | fault s =>
    simp [resultBehaviour, Behaviour.bind, Behaviour.possible, resultWithPayload]
    ext outcome
    cases outcome <;> simp [Outcome.bind]
  | diverge =>
    simp [resultBehaviour, Behaviour.bind, Behaviour.possible, resultWithPayload]
    ext outcome
    cases outcome <;> simp [Outcome.bind]
  | ub => simp [resultBehaviour, resultWithPayload]

theorem compare_iff (bits bits' : Tag → Bool) (r t : Result 2 states) :
    compare bits bits' r t = true ↔
      resultWithPayload (fun i => exitPayload (some (bits i))) r ≤
        resultWithPayload (fun i => exitPayload (some (bits' i))) t := by
  cases r <;> cases t <;> simp [LiveBit.compare, Result.refines, resultWithPayload, WithTop.coe_le_coe]
  rename_i i s j t
  cases bits i <;> cases bits' j <;> simp [exitPayload, Recognize.bitValue]

private theorem literal_query_agrees (literals : Φ → Option Bool) (op : Φ) :
    ∀ arg : Syntax.Payload Bit,
      rawWithLiterals literals op (Recognize.encodeValue ULift.up arg.val) =
        (query op arg >>= fun p => pure (Recognize.replyValue ULift.up p.down)) := by
  rintro ⟨value, typed⟩
  cases typed with
  | inl typed => cases typed; exact query_agrees op ⟨.inl .unit, .inl .unit⟩
  | inr typed => cases typed; exact query_agrees op ⟨.inr .unit, .inr .unit⟩

private theorem literal_agreement (literals : Φ → Option Bool) (exitOp : Tag → Φ) (bits : Tag → Bool)
    (agrees : ∀ i, literals (exitOp i) = some (bits i)) :
    Recognize.LiveAgreement (profile exitOp bits) (rawWithLiterals literals) := by
  intro i f bit h
  have eq : (exitOp i, bits i) = (f, bit) := Option.some.inj h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
  simp [rawWithLiterals, agrees]

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {seed reg : V} {names : Fin 5 ≃ K}
  {source target : CFG V K P.Instr} {op op' : P.Instr}
  {a : Admission P (Recognize.interface seed names) (fields reg) source}
  {b : Admission P (Recognize.interface seed names) (fields reg) target}
  {bits bits' : Tag → Bool} {exitOp exitOp' : Tag → P.Instr}

theorem observeNamed_runFinite (checked : Recognize.Checked a op (fun i => some (exitOp i)))
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (seedValue : input seed = Recognize.encodeValue ULift.up caller.val)
    (literals : P.Instr → Option Bool) (agrees : ∀ i, literals (exitOp i) = some (bits i))
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (s : Fin states) (selected : Tag → Bool) :
    LiveBit.observeNamed source names reg input literals prim s selected =
      resultWithPayload (fun i => exitPayload (some (bits i)))
        ((withSelectedExits op checked.routes selected).runFinite caller prim configs stores ⟨0, caller⟩ s) := by
  let c := checked.correspondsWith (profile := profile exitOp bits) ULift.up query
    (rawWithLiterals literals) (fun r => input r.1) (literal_query_agrees literals op)
    (literal_agreement literals exitOp bits agrees) caller seedValue
  have classified := observe_decoded_runFinite (withSelectedExits op checked.routes selected)
    caller prim configs stores (exitResult (fun i => some (bits i))) decode
    (fun i => exitPayload (some (bits i))) (decode_output bits) ⟨0, caller⟩ s PayloadType
  rw [step_selected] at classified
  exact (congrArg (fun tree => decorate prim selected (FixedCarrier.observe prim tree s decode) PayloadType)
    c.observe_eq).trans classified

theorem observeNamed_native [DecidableEq P.Instr]
    (checked : Recognize.Checked a op (fun i => some (exitOp i)))
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (seedValue : input seed = Recognize.encodeValue ULift.up caller.val)
    (literals : P.Instr → Option Bool) (agrees : ∀ i, literals (exitOp i) = some (bits i))
    (prim : Syntax.Primitives P.Instr states) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native : Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op checked.routes).checkNative native = true)
    (s : Fin states) (selected : Tag → Bool) :
    LiveBit.observeNamed source names reg input literals prim s selected =
      Shape.denote (nativeEndpoint native bits selected)
        (Syntax.model prim ((guardedTable op checked.routes).bindings caller)) s := by
  let g := withSelectedExits op checked.routes selected
  have nativeResult := (g.observe_entry native readback caller prim s).trans
    (g.observe_runFinite caller prim configs stores ⟨0, caller⟩ s)
  rw [observeNamed_runFinite checked caller input seedValue literals agrees prim configs stores s selected]
  symm
  exact (congrArg (fun (observed : Behaviour Exits.length Unit (Fin states)) => observed.bind
    (fun i a t => LambdaSSA.UB.Overlay.denote (.native (nativeExit bits i))
      (extendModel (Syntax.model prim (g.bindings caller)).raw a) t)) nativeResult).trans
    (append_payload prim caller bits _)

theorem acceptance_iff [DecidableEq P.Instr]
    (left : Recognize.Checked a op (fun i => some (exitOp i)))
    (right : Recognize.Checked b op' (fun i => some (exitOp' i)))
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (seedValue : input seed = Recognize.encodeValue ULift.up caller.val)
    (literals : P.Instr → Option Bool) (agrees : ∀ i, literals (exitOp i) = some (bits i))
    (agrees' : ∀ i, literals (exitOp' i) = some (bits' i))
    (replies : ReplyEnumeration (Recognize.signature P.Instr)) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native native' : Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op left.routes).checkNative native = true)
    (readback' : (guardedTable op' right.routes).checkNative native' = true)
    (selected selected' : Tag → Bool) :
    check? op op' left.routes right.routes native native' bits bits' selected selected'
        caller replies configs stores = some true ↔
      ∀ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        LiveBit.observeNamed source names reg input literals prim s selected ≤
          LiveBit.observeNamed target names reg input literals prim s selected' := by
  have l : (withSelectedExits op left.routes selected).checkNative native = true := readback
  have r : (withSelectedExits op' right.routes selected').checkNative native' = true := readback'
  simp only [check?, l, r, Bool.and_self, ↓reduceIte, Option.some.injEq, Table.checkAllInterpretersBy_iff]
  refine forall_congr' fun prim => forall_congr' fun s => ?_
  rw [observeNamed_runFinite left caller input seedValue literals agrees prim configs stores s selected,
    observeNamed_runFinite right caller input seedValue literals agrees' prim configs stores s selected']
  exact compare_iff bits bits' _ _

theorem rejection_iff [DecidableEq P.Instr]
    (left : Recognize.Checked a op (fun i => some (exitOp i)))
    (right : Recognize.Checked b op' (fun i => some (exitOp' i)))
    (caller : Syntax.Payload Bit) (input : V → Value Runtime)
    (seedValue : input seed = Recognize.encodeValue ULift.up caller.val)
    (literals : P.Instr → Option Bool) (agrees : ∀ i, literals (exitOp i) = some (bits i))
    (agrees' : ∀ i, literals (exitOp' i) = some (bits' i))
    (replies : ReplyEnumeration (Recognize.signature P.Instr)) (configs : ConfigurationEnumeration Packets)
    (stores : StateInventory states) (native native' : Typed P.Instr [Bit] Exits)
    (readback : (guardedTable op left.routes).checkNative native = true)
    (readback' : (guardedTable op' right.routes).checkNative native' = true)
    (selected selected' : Tag → Bool) :
    check? op op' left.routes right.routes native native' bits bits' selected selected'
        caller replies configs stores = some false ↔
      ∃ (prim : Syntax.Primitives P.Instr states) (s : Fin states),
        ¬ LiveBit.observeNamed source names reg input literals prim s selected ≤
          LiveBit.observeNamed target names reg input literals prim s selected' := by
  classical
  have h := acceptance_iff left right caller input seedValue literals agrees agrees' replies configs stores native native' readback readback'
    selected selected'
  have l : (withSelectedExits op left.routes selected).checkNative native = true := readback
  have r : (withSelectedExits op' right.routes selected').checkNative native' = true := readback'
  simp only [check?, l, r, Bool.and_self, ↓reduceIte, Option.some.injEq] at h ⊢
  simp only [Bool.eq_false_iff, ne_eq, h, not_forall]

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.LiveBit
