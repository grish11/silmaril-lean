module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
open CFG.Dependent (Packet internal_type external_type exitLabel unpack)
open CFG.Dependent.Native (withExitUB denote_exitContinuation)
open ScheduleSearch (StateInventory)
open Syntax (Payload Primitives model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {A : Syntax.Ty} {states results : Nat}

private theorem cast_value {X Y : Syntax.Ty} (h : X = Y) (p : Payload X) :
    (cast (congrArg Payload h) p).val = p.val := by cases h; rfl

private theorem returnPacket_value (g : Endpoint S R A) (caller : Payload (R.get g.control.entry))
    (p : Packet R) (i : Tag) :
    (g.returnPacket caller p i).2.val = ((g.output p.1).eval ((g.control.bindings caller).push p.2)).val :=
  cast_value (exit_type (A := A) i).symm _

def routed {R : List Syntax.Ty} (g : Endpoint S R A) (caller : Payload (R.get g.control.entry))
    (p : Packet R) : Transition R states → Behaviour (R ++ Exits A).length Unit (Fin states)
  | .exit i _ t => WithTop.some {Feedback.external R (Exits A) (.ret i (g.returnPacket caller p i).2.val t)}
  | .repeat next t => WithTop.some {Outcome.ret (Feedback.internal R (Exits A) next.1) next.2.val t}
  | .fault t => WithTop.some {Outcome.fault t}
  | .diverge => WithTop.some {Outcome.diverge}

theorem raw_step (g : Endpoint S R A) (caller : Payload (R.get g.control.entry)) (prim : Primitives Φ states)
    (config : Packet R) (s : Fin states) :
    g.feedback caller prim (blockPoint config s) = routed g caller config ((g.control.head caller config).execute prim s) := by
  obtain ⟨i, incoming⟩ := config
  rw [Table.head]
  split
  · rename_i j rowEq
    change denote (.native (g.blocks i)) (extendModel (model prim (g.control.bindings caller)).raw incoming.val) s =
      WithTop.some {Feedback.external R (Exits A) (.ret j (g.returnPacket caller ⟨i, incoming⟩ j).2.val s)}
    rw [Syntax.denote_push prim _ incoming, Endpoint.blocks, rowEq, returnPacket_value]
    exact CFG.observe_jump (L := R ++ Exits A) prim ((g.control.bindings caller).push incoming)
      (exitLabel R (Exits A) j) ((external_type (R := R) (L := Exits A) j).trans (exit_type j)) (g.output i) s
  · rename_i f arg next typed rowEq
    let env := (g.control.bindings caller).push incoming
    let target (j : Fin (S.replies f).length) := Feedback.internal R (Exits A) (next j)
    let type (j : Fin (S.replies f).length) := (internal_type (L := Exits A) (next j)).trans (typed j)
    change denote (.native (g.blocks i)) (extendModel (model prim (g.control.bindings caller)).raw incoming.val) s = _
    rw [Syntax.denote_push prim _ incoming, Endpoint.blocks, rowEq]
    change Shape.denote (.native (CFG.Dependent.Native.packedRequestTo f arg
      (S.target f) target type)) (model prim env) s = _
    rw [← CFG.Dependent.Native.packedRequestTo_agrees, CFG.Dependent.observe_packedRequestTo, Head.execute]
    cases prim f (arg.eval env) s with
    | ret a t =>
      let reply := unpack (cast (congrArg Payload (S.target f)) a)
      exact congrArg (fun v : Value Unit => WithTop.some ({Outcome.ret (target reply.1) v t} : Set _))
        (cast_value (typed reply.1).symm reply.2).symm
    | fault | diverge => rfl

def carrier (codec : Fin results ≃ Packet (Exits A))
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) :
    PositionalCarrier R (Exits A) Unit (Fin states) (configs.invocations stores).length results states where
  invocation i :=
    let (p, s) := (configs.invocations stores).get i
    (p.1, p.2.val, s)
  result := codec.toEmbedding.trans Packet.erase
  final := Function.Embedding.refl _

theorem get_encode (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (p : Packet R × Fin states) :
    (configs.invocations stores).get (FixedCarrier.encode configs stores p) = p :=
  List.getElem_idxOf _

theorem close_classifies (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A))
    (caller : Payload (R.get g.control.entry)) (prim : Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) (p : Packet R) (s : Fin states) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      resultBehaviour codec (execute (g.rows codec caller prim configs stores) (FixedCarrier.encode configs stores (p, s))) := by
  let D := carrier codec configs stores
  have rows_agree (code : Fin (configs.invocations stores).length) :
      g.feedback caller prim (invocationPoint D.invocation code) =
        (g.rows codec caller prim configs stores code).routed D := by
    let input := (configs.invocations stores).get code
    change g.feedback caller prim (blockPoint input.1 input.2) = _
    rw [raw_step, Endpoint.rows]
    dsimp only
    cases (g.control.head caller input.1).execute prim input.2 with
    | exit i _ t =>
      simp only [routed, Row.routed, D, carrier, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        Function.Embedding.refl_apply, Equiv.apply_symm_apply]
      rfl
    | «repeat» next t =>
      exact (congrArg (fun (q : Packet R × Fin states) =>
        (WithTop.some {Outcome.ret (Feedback.internal R (Exits A) q.1.1) q.1.2.val q.2} :
          Behaviour (R ++ Exits A).length Unit (Fin states)))
        (get_encode configs stores (next, t))).symm
    | fault | diverge => rfl
  have closed := classify_routed D (g.rows codec caller prim configs stores)
    (FixedCarrier.encode configs stores (p, s)) rows_agree
  have start : invocationPoint D.invocation (FixedCarrier.encode configs stores (p, s)) = blockPoint p s := by
    exact congrArg (fun (input : Packet R × Fin states) => blockPoint input.1 input.2)
      (get_encode configs stores (p, s))
  rw [start] at closed
  refine closed.trans ?_
  cases execute (g.rows codec caller prim configs stores) (FixedCarrier.encode configs stores (p, s)) <;> rfl

theorem decorate_result (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A))
    (caller : Payload (R.get g.control.entry)) (prim : Primitives Φ states) (r : Result results states) :
    (resultBehaviour codec r).bind (fun i a s =>
      denote (CFG.Dependent.Native.exitContinuation (Γ := [R.get g.control.entry]) (L := Exits A) g.control.selected i)
        (extendModel (model prim (g.control.bindings caller)).raw a) s) =
      resultBehaviour codec (g.markExit codec r) := by
  simp only [denote_exitContinuation]
  cases r with
  | ret i t =>
    cases h : g.control.selected (codec i).1 <;>
      simp [Endpoint.markExit, h, resultBehaviour, Behaviour.bind, Behaviour.possible]
    ext o
    cases o <;> simp [Outcome.bind, h]
  | fault t =>
    simp [Endpoint.markExit, resultBehaviour, Behaviour.bind, Behaviour.possible]
    ext o
    cases o <;> simp [Outcome.bind]
  | diverge =>
    simp [Endpoint.markExit, resultBehaviour, Behaviour.bind, Behaviour.possible]
    ext o
    cases o <;> simp [Outcome.bind]
  | ub => simp [Endpoint.markExit, resultBehaviour]

theorem observe_entry [DecidableEq Φ] (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A))
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A)) (readback : g.checkNative raw = true)
    (caller : Payload (R.get g.control.entry)) (prim : Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) (s : Fin states) :
    Shape.denote (withExitUB raw g.control.selected) (model prim (g.control.bindings caller)) s =
      resultBehaviour codec (g.runFinite codec caller prim configs stores ⟨g.control.entry, caller⟩ s) := by
  have same : raw = g.native := Subtype.ext (CFG.Dependent.Native.sameRegion_eq readback)
  subst raw
  have start : g.feedback caller prim (.entry s) =
      WithTop.some {Outcome.ret (Feedback.internal R (Exits A) g.control.entry) caller.val s} :=
    CFG.observe_jump (L := R ++ Exits A) prim (g.control.bindings caller)
      (Feedback.internal R (Exits A) g.control.entry) (internal_type g.control.entry) (.var 0) s
  let M := (model prim (g.control.bindings caller)).raw
  change (denote (.native g.native) M s).bind _ = _
  unfold Endpoint.native
  rw [← denote_native_feedback]
  change (Feedback.close (g.feedback caller prim) (.entry s)).bind _ = _
  rw [close_branch start]
  change (Feedback.close (g.feedback caller prim) (blockPoint ⟨g.control.entry, caller⟩ s)).bind _ = _
  rw [close_classifies g codec caller prim configs stores]
  exact decorate_result g codec caller prim _

theorem result_order (codec : Fin results ≃ Packet (Exits A)) (r t : Result results states) :
    resultBehaviour codec r ≤ resultBehaviour codec t ↔ r.refines t := by
  cases r <;> cases t <;> simp [resultBehaviour, Result.refines, WithTop.coe_le_coe]
  rename_i i s j t
  constructor
  · rintro ⟨tag, value, state⟩
    exact ⟨codec.injective (Packet.raw_injective (Prod.ext tag value)), state⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩

theorem runFinite_congr (g : Endpoint S R A) (codec : Fin results ≃ Packet (Exits A))
    (caller : Payload (R.get g.control.entry))
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) {prim other : Primitives Φ states}
    (agree : ∀ q ∈ g.control.queries caller configs stores, q.read prim = q.read other)
    (p : Packet R) (s : Fin states) :
    g.runFinite codec caller prim configs stores p s = g.runFinite codec caller other configs stores p s := by
  have same : g.rows codec caller prim configs stores = g.rows codec caller other configs stores := by
    funext code
    unfold Endpoint.rows
    dsimp only
    rw [g.control.head_execute_congr caller configs stores agree]
  simp only [Endpoint.runFinite, same]

theorem acceptance_iff [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A))
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.control.entry] (Exits A))
    (codec : Fin results ≃ Packet (Exits A)) (caller : Payload (R.get g.control.entry))
    (caller' : Payload (T.get h.control.entry)) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) (stores : StateInventory states)
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkAllInterpreters? h raw raw' codec caller caller' replies left right stores = some true ↔
      ∀ (prim : Primitives Φ states) (s : Fin states),
        Shape.denote (withExitUB raw g.control.selected) (model prim (g.control.bindings caller)) s ≤
          Shape.denote (withExitUB raw' h.control.selected) (model prim (h.control.bindings caller')) s := by
  simp only [Endpoint.checkAllInterpreters?, hg, hh, Bool.and_self, ↓reduceIte, Option.some.injEq,
    Endpoint.checkAllInterpreters]
  rw [InterpreterScript.checkAll_iff]
  · refine forall_congr' fun prim => forall_congr' fun s => ?_
    rw [observe_entry g codec raw hg caller prim left stores s,
      observe_entry h codec raw' hh caller' prim right stores s, result_order, decide_eq_true_eq]
  · intro prim other agrees s
    rw [runFinite_congr g codec caller left stores
        (fun q mem => agrees q (List.mem_dedup.mpr (List.mem_append_left _ mem))),
      runFinite_congr h codec caller' right stores
        (fun q mem => agrees q (List.mem_dedup.mpr (List.mem_append_right _ mem)))]

theorem unit_native (g : Table S R) : (Endpoint.unit g).native = g.native := by
  have same : (Endpoint.unit g).blocks = g.blocks := by
    funext i
    unfold Endpoint.blocks Table.blocks
    simp only [Endpoint.unit]
    cases g.row i <;> rfl
  apply Subtype.ext
  change nativeFeedback (Endpoint.unit g).entryRegion (Endpoint.unit g).blocks =
    nativeFeedback g.entryRegion g.blocks
  rw [same]
  rfl

theorem rejection_iff [DecidableEq Φ] (g : Endpoint S R A) (h : Endpoint S T A)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.control.entry] (Exits A))
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.control.entry] (Exits A))
    (codec : Fin results ≃ Packet (Exits A)) (caller : Payload (R.get g.control.entry))
    (caller' : Payload (T.get h.control.entry)) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) (stores : StateInventory states)
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkAllInterpreters? h raw raw' codec caller caller' replies left right stores = some false ↔
      ∃ (prim : Primitives Φ states) (s : Fin states),
        ¬ Shape.denote (withExitUB raw g.control.selected) (model prim (g.control.bindings caller)) s ≤
          Shape.denote (withExitUB raw' h.control.selected) (model prim (h.control.bindings caller')) s := by
  classical
  have valid := acceptance_iff g h raw raw' codec caller caller' replies left right stores hg hh
  simp only [Endpoint.checkAllInterpreters?, hg, hh, Bool.and_self, ↓reduceIte, Option.some.injEq] at valid ⊢
  simp only [Bool.eq_false_iff, ne_eq, valid, not_forall]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload
