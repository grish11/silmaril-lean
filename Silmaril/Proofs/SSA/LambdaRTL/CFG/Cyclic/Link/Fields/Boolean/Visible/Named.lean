module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Defs
import Silmaril.Semantics.ITree.Trace.Finite.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible

open Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event transition evaluate)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeModel treeExitNumber treeNumber)
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link (Label)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean (packets)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible

variable {F : Type} {a b : Nat} (program : Program F a b)

open Program (Address Atom Register Result State bit encode primitive store)

private def encodeState (s : program.State) : program.Address × Value Atom :=
  (⟨s.down.1⟩, encode s.down.2)

private def encodeResult (r : Result b) : program.Address × Value Atom :=
  (⟨.inr r.down.1⟩, encode r.down.2)

private theorem output_injective : Function.Injective (Program.renderResult (b := b)) := by
  rintro ⟨left, x⟩ ⟨right, y⟩ equal
  have labels : left = right := Fin.ext (congrArg Prod.fst equal)
  subst right
  have flags : x = y := by
    have packets := congrArg Prod.snd equal
    cases x <;> cases y <;> simp_all [Program.renderResult, encode, bit]
  subst y
  rfl

private theorem numbered (r : Result b) :
    treeExitNumber program.exits (encodeResult program r) = Program.renderResult r := by
  rcases r with ⟨port, flag⟩
  let index : Fin program.exits.length := ⟨port, by simp [Program.exits]⟩
  let isPort (x : program.Address) := decide ((⟨.inr port⟩ : program.Address) = x)
  have found : program.exits.findFinIdx? isPort = some index := by
    apply List.findFinIdx?_eq_some_iff.mpr
    constructor
    · simp [Program.exits, index, isPort]
    · intro j hj
      change ¬ isPort (program.exits[j.val]'j.isLt)
      simp [Program.exits, isPort]
      intro same
      exact (Nat.ne_of_gt hj) (congrArg (fun x : Fin b => x.val) same)
  change ((Option.map Fin.val (program.exits.findFinIdx? isPort)).getD program.exits.length, _) = _
  rw [found]
  rfl

private theorem lookup_internal {I : Type} {K D : Type 1} [DecidableEq K]
    (key : I → K) (injective : Function.Injective key) (body : I → D) (keys : List I) (index : I)
    (member : index ∈ keys) :
    (keys.map fun i => (key i, body i)).lookup (key index) = some (body index) := by
  induction keys with
  | nil => simp at member
  | cons first rest ih =>
    classical
    by_cases same : index = first
    · subst first
      simp
    · have miss : key index ≠ key first := fun h => same (injective h)
      simp only [List.map_cons, List.lookup_cons, beq_false_of_ne miss]
      exact ih ((List.mem_cons.mp member).resolve_left same)

private theorem lookup_external {I : Type} {K D : Type 1} [DecidableEq K]
    (key : I → K) (body : I → D) (keys : List I) (port : K)
    (outside : ∀ i, port ≠ key i) :
    (keys.map fun i => (key i, body i)).lookup port = none := by
  apply List.lookup_eq_none_iff.mpr
  rintro item member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  simpa using outside index

private theorem ret_eq_pure {Q : Type} {X : Type 1} (x : X) : (ret x : Tree (Event Q) X) = pure x := rfl

private theorem step_square (input : Fin a) (flag : Bool) (s : program.State) :
    (transition program.step s >>= fun outcome =>
      pure (outcome.map (encodeResult program) (encodeState program))) =
    Cyclic.stepSSA (treeModel.{0, 0} primitive) (program.compile input).blocks (store flag) (encodeState program s) := by
  rcases s with ⟨label, value⟩
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
    cases row : program.block index <;> cases value <;>
      simp [body, Program.step, transition, ret_eq_pure, row, Program.compiledBlock,
        Body.evalJump, Body.exec, Term.exec, Op.eval, Val.eval, upd, treeModel, encodeState, encode, bit, primitive,
        ← bind_pure_comp]

theorem observe_eq (input : Fin a) (flag : Bool) :
    program.observe input flag =
      (evaluate program.step (program.start input flag) >>= fun r => pure (Program.renderResult r)) := by
  let f := transition program.step
  let f' := mapReturn f (fun r => pure (encodeResult program r))
  let g := Cyclic.stepSSA (treeModel.{0, 0} primitive) (program.compile input).blocks (store flag)
  have commutes : (f' >=> liftPure (Sum.map id (encodeState program))) = (liftPure (encodeState program) >=> g) := by
    funext s
    change (f' s >>= liftPure (Sum.map id (encodeState program))) = (pure (encodeState program s) >>= g)
    rw [pure_bind]
    dsimp only [g]
    rw [← step_square program input flag s]
    simp only [f', mapReturn, bind_assoc, liftPure, f]
    apply bind_congr
    intro result
    cases result <;> simp
  have transport (s : program.State) :
      (evaluate program.step s >>= fun r => pure (encodeResult program r)) = iter g (encodeState program s) := by
    have natural := congrFun (LawfulElgotMonad.naturality f (fun r => pure (encodeResult program r))) s
    have uniform := congrFun (LawfulElgotMonad.uniformity f' g (encodeState program) commutes) s
    exact (natural.trans uniform).trans (pure_bind _ _)
  unfold Program.observe
  simp only [Cyclic.runSSA, Program.compile, Body.evalJump, Body.exec, Term.exec, Val.eval, store, upd, pure_bind]
  change (iter g (encodeState program (program.start input flag)) >>= _) = _
  rw [← transport, bind_assoc]
  simp only [pure_bind, numbered]

theorem compare_at [DecidableEq F] (right : Program F a b) (input : Fin a) (flag : Bool) :
    program.refinementAt? right input flag = true ↔ TraceLE (program.observe input flag) (right.observe input flag) := by
  rw [Program.refinementAt?, Silmaril.Elgot.ITree.Finite.compare_iff _ _ program.mem_states right.mem_states,
    observe_eq, observe_eq, TraceLE.bind_pure_iff output_injective]

theorem compare_all [DecidableEq F] (right : Program F a b) :
    program.refinement? right = true ↔ ∀ input flag, TraceLE (program.observe input flag) (right.observe input flag) := by
  simp only [Program.refinement?, List.all_eq_true, List.mem_finRange, forall_const, compare_at]
  constructor
  · intro accepted input flag
    have seen : (fun _ : Fin 1 => flag) ∈ packets 1 := by
      cases flag <;> simp [packets, Fin.cons, funext_iff]
    exact accepted input _ seen
  · exact fun accepted input packet _ => accepted input (packet 0)

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible
