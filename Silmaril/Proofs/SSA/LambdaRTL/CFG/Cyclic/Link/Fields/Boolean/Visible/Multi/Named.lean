module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Defs
import Silmaril.Semantics.ITree.Trace.Finite.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi.Block

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi

open Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event transition evaluate)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeExitNumber)
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link (Label)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean (Packet)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime
  (lookup_internal lookup_external ret_eq_pure iter_simulate)

variable {F : Type} {a b n : Nat} (program : Program F a b n)

private def encodeState (s : program.State) : program.Address × Value Atom :=
  (⟨s.down.1⟩, encode s.down.2)

private def encodeResult (r : Program.Result b n) : program.Address × Value Atom :=
  (⟨.inr r.down.1⟩, encode r.down.2)

theorem render_injective : Function.Injective (Program.renderResult (b := b) (n := n)) := by
  rintro ⟨left, packet⟩ ⟨right, packet'⟩ equal
  have ports : left = right := Fin.ext (congrArg Prod.fst equal)
  have packets : packet = packet' := encode_injective (congrArg Prod.snd equal)
  subst right
  subst packet'
  rfl

private theorem numbered (r : Program.Result b n) :
    treeExitNumber program.exits (encodeResult program r) = Program.renderResult r :=
  Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.VisibleRuntime.numbered r.down.1 (encode r.down.2)

private theorem step_square (input : Fin a) (packet : Packet n) (s : program.State) :
    (transition program.step s >>= fun outcome =>
      pure (outcome.map (encodeResult program) (encodeState program))) =
    Cyclic.stepSSA (model F) (program.compile input).blocks (store packet) (encodeState program s) := by
  rcases s with ⟨label, fields⟩
  let key (i : Fin program.locals) : program.Address := ⟨.inl i⟩
  let body i := program.compiledBlock (program.block i)
  let keys := List.finRange program.locals
  cases label with
  | inr port =>
    have outside (i : Fin program.locals) : (⟨.inr port⟩ : program.Address) ≠ key i := by
      intro equal
      have impossible : (Sum.inr port : Label program.locals b) = Sum.inl i :=
        congrArg (fun x : program.Address => x.down) equal
      cases impossible
    have lookup := lookup_external key body keys ⟨.inr port⟩ outside
    simp only [Program.compile, Cyclic.stepSSA, encodeState]
    rw [lookup]
    simp [Program.step, transition, ret_eq_pure, encodeResult]
  | inl index =>
    have injective : Function.Injective key := fun _ _ h => Sum.inl.inj (congrArg ULift.down h)
    have lookup := lookup_internal key injective body keys index (List.mem_finRange _)
    simp only [Program.compile, Cyclic.stepSSA, encodeState]
    rw [lookup]
    change _ = Sum.inr <$> (program.compiledBlock (program.block index)).body.evalJump
      (model F) (upd (store packet) cursor (encode fields))
    rw [eval_block]
    cases row : program.block index <;>
      simp [Program.step, transition, ret_eq_pure, row, encodeState, ← bind_pure_comp]

theorem observe_eq (input : Fin a) (packet : Packet n) :
    program.observe input packet =
      (evaluate program.step (program.start input packet) >>= fun r => pure (Program.renderResult r)) := by
  let f := transition program.step
  let g := Cyclic.stepSSA (model F) (program.compile input).blocks (store packet)
  have transport := iter_simulate f g (encodeState program) (encodeResult program)
    (step_square program input packet)
  have entry : (program.compile input).entry.evalJump (model F) (store packet) =
      pure (encodeState program (program.start input packet)) := by
    simp [Program.compile, Body.evalJump, Body.exec, Term.exec, Val.eval, store, upd, encodeState, Program.start]
  unfold Program.observe Cyclic.runSSA
  rw [entry, pure_bind]
  change (iter g (encodeState program (program.start input packet)) >>= _) = _
  rw [← transport, bind_assoc]
  simp only [pure_bind, numbered]
  rfl

theorem compare_at [DecidableEq F] (right : Program F a b n) (input : Fin a) (packet : Packet n) :
    program.refinementAt? right input packet = true ↔
      TraceLE (program.observe input packet) (right.observe input packet) := by
  rw [Program.refinementAt?, Silmaril.Elgot.ITree.Finite.compare_iff _ _ program.mem_states right.mem_states,
    observe_eq, observe_eq, TraceLE.bind_pure_iff render_injective]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Multi
