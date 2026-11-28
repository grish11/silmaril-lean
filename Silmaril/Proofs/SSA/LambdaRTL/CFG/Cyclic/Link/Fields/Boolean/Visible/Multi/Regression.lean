module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Packed.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Defs

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi

open Silmaril.Elgot.ITree (HasTrace TraceLE hasTrace_bind_pure_iff hasTrace_vis_exchange_iff
  out out_injective out_vis out_ret vis ret vis_bind)
open Silmaril.Elgot.ITree.Finite (Head)
open Silmaril.Elgot.ITree.Finite (Event evaluate headFrom out_evaluate)

private def bits (changing retained : Bool) : Packet 2 :=
  Fin.cons changing (Fin.cons retained Fin.elim0)

-- A reply writes field 0 and takes the backedge. Once field 0 is true,
-- field 1 selects the exit port.
private def route (useRetained : Bool) : Program Unit 1 2 2 where
  locals := 3
  entry _ := .inl 0
  block i :=
    if i = 0 then .branch 0 (.inl 2) (.inl 1)
    else if i = 1 then .apply () 0 0 (.inl 0)
    else if useRetained then .branch 1 (.inr 1) (.inr 0)
    else .jump (.inr 0)

private abbrev retained := route true
private abbrev ignoresRetained := route false

private def afterReply (packet : Packet 2) : Option (Fin 2 × Packet 2) :=
  match headFrom retained.step retained.states (retained.start 0 packet) with
  | .request ((), false) next =>
    match headFrom retained.step retained.states (next true) with
    | .result result => some result.down
    | _ => none
  | _ => none

example : afterReply (bits false true) = some (1, bits true true) := by
  have fields : replace (bits false true) 0 true = bits true true := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [replace, bits]
  cbv
  exact congrArg (fun p => some (1, p)) fields

example : afterReply (bits false false) = some (0, bits true false) := by
  have fields : replace (bits false false) 0 true = bits true false := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [replace, bits]
  cbv
  exact congrArg (fun p => some (0, p)) fields

private def back (reply : Bool) : retained.State :=
  ⟨retained.entry 0, replace (bits false true) 0 reply⟩

private theorem firstRequest :
    headFrom retained.step retained.states (retained.start 0 (bits false true)) =
      .request ((), false) back := by cbv

private theorem keptExit :
    headFrom retained.step retained.states (back true) = .result ⟨1, bits true true⟩ := by
  have fields : replace (bits false true) 0 true = bits true true := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [replace, bits]
  cbv
  let result (p : Packet 2) : Head (Unit × Bool) (Program.Result 2 2) retained.State := .result ⟨1, p⟩
  exact congrArg result fields

-- The actual named runner returns through port 1 with both fields true.
private theorem keptTrace : HasTrace (retained.observe 0 (bits false true))
    (.exchange (.ask ((), false)) true (.result (1, encode (bits true true)))) := by
  rw [Program.observe_eq, hasTrace_bind_pure_iff]
  refine ⟨.exchange (.ask ((), false)) true (.result ⟨1, bits true true⟩), ?_, rfl⟩
  refine ⟨evaluate retained.step ∘ back, ?_, ?_⟩
  · rw [out_evaluate _ _ retained.mem_states, firstRequest]
    rfl
  · change out (evaluate retained.step (back true)) = Part.some (.ret ⟨1, bits true true⟩)
    rw [out_evaluate _ _ retained.mem_states, keptExit]
    rfl

private def backIgnored (reply : Bool) : ignoresRetained.State :=
  ⟨ignoresRetained.entry 0, replace (bits false true) 0 reply⟩

private theorem ignoredRequest :
    headFrom ignoresRetained.step ignoresRetained.states (ignoresRetained.start 0 (bits false true)) =
      .request ((), false) backIgnored := by cbv

private theorem ignoredExit :
    headFrom ignoresRetained.step ignoresRetained.states (backIgnored true) =
      .result ⟨0, replace (bits false true) 0 true⟩ := by cbv

private theorem missingTrace : ¬ HasTrace (ignoresRetained.observe 0 (bits false true))
    (.exchange (.ask ((), false)) true (.result (1, encode (bits true true)))) := by
  have request : evaluate ignoresRetained.step (ignoresRetained.start 0 (bits false true)) =
      vis (.ask ((), false)) (evaluate ignoresRetained.step ∘ backIgnored) := by
    apply out_injective
    rw [out_evaluate _ _ ignoresRetained.mem_states, ignoredRequest, out_vis]
    rfl
  let result : Program.Result 2 2 := ⟨0, replace (bits false true) 0 true⟩
  have returns : evaluate ignoresRetained.step (backIgnored true) = ret result := by
    apply out_injective
    rw [out_evaluate _ _ ignoresRetained.mem_states, ignoredExit, out_ret]
    rfl
  rw [Program.observe_eq, request, vis_bind, hasTrace_vis_exchange_iff]
  change ¬ HasTrace (evaluate ignoresRetained.step (backIgnored true) >>= fun r => pure (Program.renderResult r)) _
  rw [returns, show (ret result >>= fun r => pure (Program.renderResult r)) = ret (Program.renderResult result)
    from pure_bind _ _]
  simp [HasTrace, Program.renderResult, result]

example : ¬ TraceLE (retained.observe 0 (bits false true)) (ignoresRetained.observe 0 (bits false true)) :=
  fun included => missingTrace (included _ keptTrace)

private theorem rejected :
    retained.refinementAt? ignoresRetained 0 (bits false true) = false := by
  cases verdict : retained.refinementAt? ignoresRetained 0 (bits false true) with
  | false => rfl
  | true =>
    have included := (retained.refinementAt?_iff ignoresRetained 0 (bits false true)).mp verdict
    exact (missingTrace (included _ keptTrace)).elim

-- Exercise the whole executable product on both initial values of the retained field.
#guard !(retained.refinementAt? ignoresRetained 0 (bits false true))
#guard retained.refinementAt? ignoresRetained 0 (bits false false)

section Packed

open Silmaril (Ty HasTy)
open Silmaril.Isotope (BoundCtx)
open Silmaril.Isotope.Bridge.NamedFlat (elaborate check_sound)
open Silmaril.Isotope.Bridge.NamedFlat.Capture (packEnv)
open Silmaril.Isotope.LambdaSSA (FiniteCFG)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)

private def boolean : Ty Empty := .coprod .unit .unit
private def packetType : Ty Empty := .product boolean (.product boolean .unit)
private def captureTypes : BoundCtx (Ty Empty) 1 := .snoc .nil packetType
private def capture : Fin 1 → Register 2 := fun _ => cursor

private instance : HasTy Unit (Ty Empty) := ⟨fun _ => boolean, fun _ => boolean⟩

private def leftTarget := (elaborate (retained.compile 0) retained.exits capture).get (by decide)
private def rightTarget := (elaborate (ignoresRetained.compile 0) ignoresRetained.exits capture).get (by decide)

private theorem leftTyped : leftTarget.HasType captureTypes (fun _ => packetType) (fun _ => packetType) :=
  check_sound leftTarget captureTypes (fun _ => packetType) (fun _ => packetType) (by decide)

private theorem rightTyped : rightTarget.HasType captureTypes (fun _ => packetType) (fun _ => packetType) :=
  check_sound rightTarget captureTypes (fun _ => packetType) (fun _ => packetType) (by decide)

private def env : Env Atom := fun _ => encode (bits false true)
private def ambient : Env Atom := fun _ => .unit

example : ¬ TraceLE
    (region Visible.Program.primitive (extend ambient (packEnv 1 env))
      ((FiniteCFG.packedExecutionRegion leftTyped).packInputsDestructure captureTypes.toList))
    (region Visible.Program.primitive (extend ambient (packEnv 1 env))
      ((FiniteCFG.packedExecutionRegion rightTyped).packInputsDestructure captureTypes.toList)) := by
  intro included
  have left := retained.packed_observe 0 (bits false true) capture rfl leftTyped ambient env (fun _ => rfl)
  have right := ignoresRetained.packed_observe 0 (bits false true) capture rfl rightTyped ambient env (fun _ => rfl)
  have included' := congrArg₂ TraceLE left right ▸ included
  have accepted := (retained.refinementAt?_iff_packedOutput ignoresRetained 0 (bits false true)).mpr included'
  simp [rejected] at accepted

end Packed

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi
