module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Conservativity.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (evaluate headFrom out_evaluate)
open Silmaril.Isotope (BoundCtx)
open Silmaril.Isotope.Bridge.NamedFlat (elaborate check_sound)
open Silmaril.Isotope.Bridge.NamedFlat.Capture (packEnv)
open Silmaril.Isotope.LambdaSSA (FiniteCFG)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)

private def signature : PrimitiveSignature Unit :=
  ⟨fun _ => .unit, fun _ => .empty⟩

private def profile : Fin 1 → PacketType := fun _ => .unit

-- A request with no replies still reaches a visible head. The continuation
-- is well typed and cannot be taken. The other graph only has a silent loop.
private def fixture (request : Bool) : Program signature profile profile where
  locals := 1
  localType := profile
  entry _ := .inl 0
  entryType _ := rfl
  block _ := if request then .apply () .unit (.inl 0) .unit else .term (.jump (.inl 0) (.var .here))

private abbrev waiting := fixture true
private abbrev looping := fixture false

private def key : signature.Request := ⟨(), ⟨⟩⟩
private def packet : Denote (profile 0) := ⟨⟩

private theorem looping_diverges : looping.observe 0 packet = diverge := by
  have head : headFrom looping.step looping.states (looping.start 0 packet) = .stop := by cbv
  have root : evaluate looping.step (looping.start 0 packet) = diverge := by
    apply out_injective
    rw [out_evaluate _ _ looping.mem_states, head, out_diverge]
    rfl
  rw [Program.observe_eq, root, diverge_bind]

private theorem waiting_request : HasTrace (waiting.observe 0 packet) (.request (.ask key)) := by
  let next : signature.Reply key → waiting.State := fun _ => waiting.start 0 packet
  have head : headFrom waiting.step waiting.states (waiting.start 0 packet) = .request key next := by cbv
  have root : evaluate waiting.step (waiting.start 0 packet) = vis (.ask key) (evaluate waiting.step ∘ next) := by
    apply out_injective
    rw [out_evaluate _ _ waiting.mem_states, head, out_vis]
    rfl
  rw [Program.observe_eq, root, vis_bind]
  exact hasTrace_vis_request _ _

example : TraceLE (looping.observe 0 packet) (waiting.observe 0 packet) :=
  looping_diverges ▸ traceLE_diverge _

private theorem distinct : looping.observe 0 packet ≠ waiting.observe 0 packet := by
  intro equal
  have invisible := equal.symm ▸ waiting_request
  rw [looping_diverges, hasTrace_diverge_iff] at invisible
  cases invisible

#guard looping.refinementAt? waiting 0 packet
#guard !(waiting.refinementAt? looping 0 packet)
#guard !(looping.weakEqAt? waiting 0 packet)
#guard waiting.weakEqAt? waiting 0 packet

private def pendingWitness : Program.Mismatch signature profile :=
  ⟨⟨0, packet⟩, .rightToLeft, .request (.ask key)⟩

example : looping.explainMismatch? waiting = some pendingWitness := by cbv

private def captureTypes : BoundCtx PacketType 1 := .snoc .nil .unit
private def captures : Fin 1 → Register := fun _ => ⟨0⟩
private instance : Silmaril.HasTy Unit PacketType := signature.typing

private def waitingTarget := (elaborate (waiting.compile 0) waiting.exits captures).get (by decide)
private def loopingTarget := (elaborate (looping.compile 0) looping.exits captures).get (by decide)

private theorem waitingTyped : waitingTarget.HasType captureTypes profile profile :=
  check_sound waitingTarget captureTypes profile profile (by decide)

private theorem loopingTyped : loopingTarget.HasType captureTypes profile profile :=
  check_sound loopingTarget captureTypes profile profile (by decide)

private def env : Silmaril.Isotope.LambdaSSA.Semantics.Env Atom := fun _ => .unit

private noncomputable def packedRun {target : FiniteCFG Unit 1 1 1}
    (typed : target.HasType captureTypes profile profile) :=
  region signature.primitive (Silmaril.Isotope.LambdaSSA.Semantics.extend env (packEnv 1 env))
    ((FiniteCFG.packedExecutionRegion typed).packInputsDestructure captureTypes.toList)

private theorem distinctPacked : packedRun loopingTyped ≠ packedRun waitingTyped := by
  intro equal
  have left := looping.packed_observe 0 packet captures rfl loopingTyped env env (fun _ => rfl)
  have right := waiting.packed_observe 0 packet captures rfl waitingTyped env env (fun _ => rfl)
  have tagged := left.symm.trans (equal.trans right)
  exact distinct ((looping.weakEqAt?_iff waiting 0 packet).mp
    ((looping.weakEqAt?_iff_packedOutput waiting 0 packet).mpr tagged))

private def packedLoop : Program.PackedEntry looping 0 :=
  ⟨1, captures, captureTypes, profile, profile, loopingTarget, rfl, loopingTyped⟩

private def packedWait : Program.PackedEntry waiting 0 :=
  ⟨1, captures, captureTypes, profile, profile, waitingTarget, rfl, waitingTyped⟩

open Silmaril.Logic.ITree

example (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature) :
    TraceInstitution.Sat policy (packedLoop.refinementSentence packedWait .leftToRight env env env env) :=
  (Program.refinementAt?_iff_valid_traceSat packet packedLoop packedWait env env env env
    (fun _ => rfl) (fun _ => rfl)).mp (by cbv) policy

-- Denying every reply still exposes the pending request in the reverse comparison.
example : ¬ TraceInstitution.Sat (signature.traceModelUnder (fun _ _ => false))
    (packedLoop.refinementSentence packedWait .rightToLeft env env env env) := by
  intro accepted
  have decision := (Program.refinementAtUnder?_iff_traceSat (fun _ _ => false) packet packedWait packedLoop
    env env env env (fun _ => rfl) (fun _ => rfl)).mpr accepted
  have rejected : waiting.refinementAtUnder? (fun _ _ => false) looping 0 packet = false := by cbv
  simp [rejected] at decision

example : ¬ (∀ policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature,
    TraceInstitution.Sat policy (packedLoop.refinementSentence packedWait .leftToRight env env env env) ∧
    TraceInstitution.Sat policy (packedLoop.refinementSentence packedWait .rightToLeft env env env env)) :=
  fun valid => distinctPacked ((packedLoop.observe_eq_iff_mutual_valid packedWait env env env env).mpr valid)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
