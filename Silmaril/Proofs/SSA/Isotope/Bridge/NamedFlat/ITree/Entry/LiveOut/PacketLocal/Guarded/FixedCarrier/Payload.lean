module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Payload.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Thms

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload

open Silmaril
open Silmaril.Isotope
open Silmaril.Elgot.ITree (Tree vis ret out_ret out_vis diverge)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (denote_exitContinuation)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint Exits resultBehaviour)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch (StateInventory)

attribute [local instance] Recognize.requestTypes

local notation "UnitExits" => LambdaSSA.UB.Overlay.Shape.TwoRequest.Exits
variable {Φ : Type} {R : List Syntax.Ty} {A : Syntax.Ty} {states results : Nat}

private def carrier (codec : Fin results ≃ Packet (Exits A)) (tree : Packet R → RunTree Φ)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) :
    PositionalCarrier Loop UnitExits (RunTree Φ) (Fin states) (configs.invocations stores).length results states where
  invocation i :=
    let (p, s) := (configs.invocations stores).get i
    (0, .atom (tree p), s)
  result := ⟨fun i => ((codec i).1, Recognize.encodeValue (fun _ => diverge) (codec i).2.val),
    fun i j eq => by
      apply codec.injective
      apply Packet.raw_injective
      change ((codec i).1, (codec i).2.val) = ((codec j).1, (codec j).2.val)
      refine Prod.ext (congrArg (fun (v : Fin 2 × Value (RunTree Φ)) => v.1) eq) ?_
      have same := congrArg (fun v => Recognize.encodeValue (fun _ => ()) v.2) eq
      simpa only [lower_lift] using same⟩
  final := Function.Embedding.refl _

private theorem get_encode (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (p : Packet R × Fin states) :
    (configs.invocations stores).get (FixedCarrier.encode configs stores p) = p :=
  List.getElem_idxOf _

theorem observe_roots (g : Endpoint (Recognize.signature Φ) R A)
    (codec : Fin results ≃ Packet (Exits A)) (caller : Syntax.Payload (R.get g.control.entry))
    (prim : Syntax.Primitives Φ states)
    (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (tree : Packet R → RunTree Φ) (roots : RootAgrees g caller tree) (decode : ExitDecoder)
    (decodes : ∀ p : Packet (Exits A), decode (packedReturn p) = some (p.1, p.2.val))
    (p : Packet R) (s : Fin states) :
    decorate prim g.control.selected (FixedCarrier.observe prim (tree p) s decode) A =
      resultBehaviour codec (g.runFinite codec caller prim configs stores p s) := by
  let D := carrier (Φ := Φ) codec tree configs stores
  have rows_agree (code : Fin (configs.invocations stores).length) :
      feedback prim decode (invocationPoint D.invocation code) =
        (g.rows codec caller prim configs stores code).routed D := by
    let input := (configs.invocations stores).get code
    change treeStep prim (tree input.1) input.2 decode = _
    rw [roots input.1, Endpoint.rows]
    dsimp only
    cases g.control.head caller input.1 with
    | exit i selected =>
      simp only [Head.execute, treeStep, out_ret, Part.some_dom, ↓reduceDIte, Part.get_some,
        decodes, terminal, Row.routed, D, carrier, Function.Embedding.refl_apply]
      exact congrArg (fun q : Packet (Exits A) =>
        let outward := Feedback.external Loop UnitExits
          (Outcome.ret q.1 (Recognize.encodeValue (fun _ => (diverge : RunTree Φ)) q.2.val) input.2)
        (WithTop.some {outward} : Behaviour (Loop ++ UnitExits).length (RunTree Φ) (Fin states)))
        (codec.apply_symm_apply (g.returnPacket caller input.1 i)).symm
    | diverge => simp [Head.execute, treeStep, terminal, Row.routed]
    | request f arg next =>
      simp only [Head.execute, treeStep, out_vis, Part.some_dom, ↓reduceDIte, Part.get_some]
      cases prim f arg input.2 with
      | ret reply t =>
        exact (congrArg (fun (q : Packet R × Fin states) =>
          (WithTop.some {Outcome.ret (Feedback.internal Loop UnitExits 0) (.atom (tree q.1)) q.2} :
            Behaviour (Loop ++ UnitExits).length (RunTree Φ) (Fin states)))
          (get_encode configs stores (_, t))).symm
      | fault | diverge => rfl
  have closed := classify_routed D (g.rows codec caller prim configs stores)
    (FixedCarrier.encode configs stores (p, s)) rows_agree
  have start : invocationPoint D.invocation (FixedCarrier.encode configs stores (p, s)) =
      .block 0 (.atom (tree p)) s :=
    congrArg (fun (q : Packet R × Fin states) => Feedback.Point.block 0 (.atom (tree q.1)) q.2)
      (get_encode configs stores (p, s))
  rw [start] at closed
  have projected (r : Result results states) :
      (r.routed D).map (Set.image project) = resultBehaviour codec r := by
    cases r <;> simp [Result.routed, D, carrier, project, resultBehaviour]
    exact ⟨rfl, lower_lift _⟩
  unfold FixedCarrier.observe Endpoint.runFinite
  rw [closed, projected]
  have decorated := g.decorate_result codec caller prim
    (execute (g.rows codec caller prim configs stores) (FixedCarrier.encode configs stores (p, s)))
  simp only [denote_exitContinuation] at decorated
  simp only [decorate, denote_exitContinuation]
  exact decorated

end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload
