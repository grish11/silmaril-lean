module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs
import Silmaril.Semantics.ITree.Trace.Finite.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Block

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (transition evaluate)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeExitNumber)
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link (Label)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.PacketType (encode)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime
  (lookup_internal lookup_external ret_eq_pure iter_simulate)

variable {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
  {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
  (program : Program signature inputs outputs)

private def encodeState (s : program.State) : program.Address × Value Atom :=
  encodeTransfer s.down

private def encodeResult (r : Program.Result outputs) : program.Address × Value Atom :=
  (⟨.inr r.down.1⟩, encode (outputs r.down.1) r.down.2)

theorem render_injective : Function.Injective (Program.renderResult (outputs := outputs)) := by
  rintro ⟨⟨left, x⟩⟩ ⟨⟨right, y⟩⟩ equal
  have ports : left = right := Fin.ext (congrArg Prod.fst equal)
  subst right
  have values : x = y := encode_injective (outputs left) (congrArg Prod.snd equal)
  subst y
  rfl

private theorem numbered (r : Program.Result outputs) :
    treeExitNumber program.exits (encodeResult program r) = Program.renderResult r :=
  Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime.numbered r.down.1 (encode (outputs r.down.1) r.down.2)

private theorem step_square (input : Fin a) (packet : Denote (inputs input)) (s : program.State) :
    (transition program.step s >>= fun outcome =>
      pure (outcome.map (encodeResult program) (encodeState program))) =
    Cyclic.stepSSA (model signature) (program.compile input).blocks (Program.store (inputs := inputs) input packet)
      (encodeState program s) := by
  rcases s with ⟨⟨label, fields⟩⟩
  let key (i : Fin program.locals) : program.Address := ⟨.inl i⟩
  let body (i : Fin program.locals) : Block Register program.Address F := ⟨⟨0⟩, (program.block i).compile⟩
  let keys := List.finRange program.locals
  cases label with
  | inr port =>
    have outside (i : Fin program.locals) : (⟨.inr port⟩ : program.Address) ≠ key i := by
      intro equal
      have impossible : (Sum.inr port : Label program.locals b) = Sum.inl i :=
        congrArg (fun x : program.Address => x.down) equal
      cases impossible
    have lookup := lookup_external key body keys ⟨.inr port⟩ outside
    simp only [Program.compile, Cyclic.stepSSA, encodeState, encodeTransfer]
    rw [lookup]
    simp [Program.step, transition, ret_eq_pure, encodeResult]
  | inl index =>
    have injective : Function.Injective key := fun _ _ h => Sum.inl.inj (congrArg ULift.down h)
    have lookup := lookup_internal key injective body keys index (List.mem_finRange _)
    simp only [Program.compile, Cyclic.stepSSA, encodeState, encodeTransfer]
    rw [lookup]
    let store := Program.store (inputs := inputs) input packet
    change Denote (program.localType index) at fields
    change _ = Sum.inr <$> (program.block index).compile.evalJump (model signature)
      (upd store ⟨0⟩ (encode (program.localType index) fields))
    rw [code_sound (program.block index) (single fields) _ (agrees_single fields store)]
    cases action : (program.block index).action (single fields) with
    | inr next =>
      simp [Program.step, transition, ret_eq_pure, action, encodeState]
    | inl request =>
      rcases request with ⟨request, next⟩
      simp [Program.step, transition, ret_eq_pure, action, encodeState, ← bind_pure_comp]

private theorem encode_cast {left right : PacketType} (equal : left = right) (packet : Denote right) :
    encode left (cast (congrArg Denote equal.symm) packet) = encode right packet := by
  cases equal
  rfl

theorem observe_eq (input : Fin a) (packet : Denote (inputs input)) :
    program.observe input packet =
      (evaluate program.step (program.start input packet) >>= fun r => pure (Program.renderResult r)) := by
  let f := transition program.step
  let g := Cyclic.stepSSA (model signature) (program.compile input).blocks (Program.store (inputs := inputs) input packet)
  have transport := iter_simulate f g (encodeState program) (encodeResult program)
    (step_square program input packet)
  have entry : (program.compile input).entry.evalJump (model signature) (Program.store (inputs := inputs) input packet) =
      pure (encodeState program (program.start input packet)) := by
    simp [Program.compile, Body.evalJump, Body.exec, Term.exec, Val.eval, Program.store, upd,
      encodeState, encodeTransfer, Program.start, encode_cast (program.entryType input) packet]
  unfold Program.observe Cyclic.runSSA
  rw [entry, pure_bind]
  change (iter g (encodeState program (program.start input packet)) >>= _) = _
  rw [← transport, bind_assoc]
  simp only [pure_bind, numbered]
  rfl

theorem compare_at [DecidableEq F] (right : Program signature inputs outputs) (input : Fin a)
    (packet : Denote (inputs input)) :
    program.refinementAt? right input packet = true ↔
      TraceLE (program.observe input packet) (right.observe input packet) := by
  rw [Program.refinementAt?, Silmaril.Elgot.ITree.Finite.compare_iff _ _ program.mem_states right.mem_states,
    observe_eq, observe_eq, TraceLE.bind_pure_iff render_injective]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
