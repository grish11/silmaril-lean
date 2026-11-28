module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible.Packed.Thms
import Silmaril.Semantics.ElgotMonads.Thms

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible

open Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Elgot.ITree.Finite (Event)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Bridge.NamedFlat (treeExitNumber)
open Program (Atom store)

private def wire : Program Unit 1 1 where
  locals := 0
  entry _ := .inr 0
  block := Fin.elim0

private def announce : Program Unit 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := .apply () (.inr 0)

private def silentLoop : Program Unit 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := .jump (.inl 0)

private def untilTrue : Program Unit 1 1 where
  locals := 2
  entry _ := .inl 0
  block index := if index = 0 then .apply () (.inl 1) else .branch (.inr 0) (.inl 0)

example : silentLoop.refinement? announce = true := by cbv
example : wire.refinement? silentLoop = false := by cbv
example : untilTrue.refinement? untilTrue = true := by cbv

-- Both machines initially request the same event. A false reply returns on
-- the left and takes the backedge on the right.
example : announce.refinement? untilTrue = false := by cbv

-- After the first request, a false reply enters a silent self-loop.
private def cycleOnFalse : Program Unit 1 1 where
  locals := 3
  entry _ := .inl 0
  block index := if index = 0 then .apply () (.inl 1)
    else if index = 1 then .branch (.inr 0) (.inl 2)
    else .jump (.inl 2)

private def afterFalse : ExchangePath (Event (Unit × Bool)) :=
  .cons (.ask ((), false)) false .nil

example : cycleOnFalse.silentAfter? 0 false .nil = false := by cbv
example : cycleOnFalse.silentAfter? 0 false (.cons (.ask ((), true)) false .nil) = false := by cbv
example : cycleOnFalse.refinementWithSilence? cycleOnFalse = true := by cbv

example : SilentAfter (cycleOnFalse.observe 0 false) afterFalse :=
  (cycleOnFalse.silentAfter?_iff 0 false afterFalse).mp (by cbv)

-- The same exchange returns in announce and exposes a second request in untilTrue.
example : ¬ SilentAfter (announce.observe 0 false) afterFalse := by
  intro seen
  have yes := (announce.silentAfter?_iff 0 false afterFalse).mpr seen
  have no : announce.silentAfter? 0 false afterFalse = false := by cbv
  simp [no] at yes

example : ¬ SilentAfter (untilTrue.observe 0 false) afterFalse := by
  intro seen
  have yes := (untilTrue.silentAfter?_iff 0 false afterFalse).mpr seen
  have no : untilTrue.silentAfter? 0 false afterFalse = false := by cbv
  simp [no] at yes

example : ∀ input flag, TraceLE (cycleOnFalse.observe input flag) (announce.observe input flag) :=
  (cycleOnFalse.refinement?_iff announce).mp (by cbv)

example : ¬ TraceLEWithSilence (cycleOnFalse.observe 0 false) (announce.observe 0 false) := by
  intro related
  have yes := (cycleOnFalse.refinementAtWithSilence?_iff announce 0 false).mpr related
  have no : cycleOnFalse.refinementAtWithSilence? announce 0 false = false := by cbv
  simp [no] at yes

private def echo : Model Unit Part (Value Atom) where
  unit := .unit
  pair := .pair
  inl := .inl
  inr := .inr
  unpair
    | .pair x y => pure (x, y)
    | _ => Part.none
  split
    | .inl x => pure (.inl x)
    | .inr y => pure (.inr y)
    | _ => Part.none
  app _ := pure
  abort _ := Part.none

private noncomputable def handled (program : Program Unit 1 1) (flag : Bool) : Part (Nat × Value Atom) :=
  CFG.Cyclic.runSSA echo (program.compile 0) (store flag) >>= fun result =>
    pure (treeExitNumber program.exits result)

private theorem handled_entry (program : Program Unit 1 1) (flag : Bool) :
    handled program flag =
      (iter (CFG.Cyclic.stepSSA echo (program.compile 0).blocks (store flag))
        (⟨program.entry 0⟩, Program.encode flag) >>= fun result => pure (treeExitNumber program.exits result)) := by
  simp only [handled, CFG.Cyclic.runSSA, Program.compile, Body.evalJump, Body.exec, Term.exec, Val.eval,
    store, upd, pure_bind, ite_eq_left trivial]

private theorem wire_echo (flag : Bool) : handled wire flag = Part.some (0, Program.encode flag) := by
  rw [handled_entry]
  let step := CFG.Cyclic.stepSSA echo (wire.compile 0).blocks (store flag)
  let result : wire.Address × Value Atom := (⟨.inr 0⟩, Program.encode flag)
  change (iter step result >>= _) = _
  have exit : step result = pure (.inl result) := rfl
  rw [congrFun (LawfulElgotMonad.fixpoint step) result, exit, pure_bind, Sum.elim_inl, pure_bind]
  rfl

private theorem announce_echo (flag : Bool) : handled announce flag = Part.some (0, Program.encode flag) := by
  rw [handled_entry]
  let step := CFG.Cyclic.stepSSA echo (announce.compile 0).blocks (store flag)
  let start : announce.Address × Value Atom := (⟨.inl ⟨0, by decide⟩⟩, Program.encode flag)
  let result : announce.Address × Value Atom := (⟨.inr 0⟩, Program.encode flag)
  change (iter step start >>= _) = _
  have head : step start = pure (.inr result) := by
    change (Sum.inr <$> (announce.compiledBlock (announce.block ⟨0, by decide⟩)).body.evalJump echo
        (upd (store flag) ⟨0⟩ (Program.encode flag))) = _
    simp [announce, Program.compiledBlock, echo, Program.encode, Body.evalJump, Body.exec,
      Term.exec, Op.eval, Val.eval, upd, result]
  have exit : step result = pure (.inl result) := rfl
  rw [congrFun (LawfulElgotMonad.fixpoint step) start, head, pure_bind, Sum.elim_inr,
    congrFun (LawfulElgotMonad.fixpoint step) result, exit, pure_bind, Sum.elim_inl, pure_bind]
  rfl

/-- The echo handler erases the request, so both actual named Part runners
have identical terminating results at every Boolean input. -/
example (flag : Bool) : handled announce flag = handled wire flag :=
  (announce_echo flag).trans (wire_echo flag).symm

/-- The weak tree comparison still detects the pending request on the left. -/
example : ¬ TraceLE (announce.observe 0 false) (wire.observe 0 false) := by
  intro traces
  have accepted := (announce.refinementAt?_iff wire 0 false).mpr traces
  have rejected : announce.refinementAt? wire 0 false = false := by cbv
  simp [rejected] at accepted

section Packed

open Silmaril (Ty HasTy)
open Silmaril.Isotope (BoundCtx)
open Silmaril.Isotope.Bridge.NamedFlat (elaborate check_sound)
open Silmaril.Isotope.Bridge.NamedFlat.Capture (packEnv)
open Silmaril.Isotope.LambdaSSA (FiniteCFG)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (region)

private def boolean : Ty Empty := .coprod .unit .unit
private def packet : Ty Empty := .product boolean .unit
private def captureTypes : BoundCtx (Ty Empty) 1 := .snoc .nil packet
private def capture : Fin 1 → Program.Register := fun _ => ⟨0⟩

private instance : HasTy Unit (Ty Empty) := ⟨fun _ => boolean, fun _ => boolean⟩

private def announceTarget := (elaborate (announce.compile 0) announce.exits capture).get (by decide)
private def wireTarget := (elaborate (wire.compile 0) wire.exits capture).get (by decide)

private theorem announceTyped : announceTarget.HasType captureTypes (fun _ => packet) (fun _ => packet) :=
  check_sound announceTarget captureTypes (fun _ => packet) (fun _ => packet) (by decide)

private theorem wireTyped : wireTarget.HasType captureTypes (fun _ => packet) (fun _ => packet) :=
  check_sound wireTarget captureTypes (fun _ => packet) (fun _ => packet) (by decide)

private def env (flag : Bool) : Env Atom := fun _ => Program.encode flag
private def ambient : Env Atom := fun _ => .unit

example : ¬ TraceLE
    (region Program.primitive (extend ambient (packEnv 1 (env false)))
      ((FiniteCFG.packedExecutionRegion announceTyped).packInputsDestructure captureTypes.toList))
    (region Program.primitive (extend ambient (packEnv 1 (env false)))
      ((FiniteCFG.packedExecutionRegion wireTyped).packInputsDestructure captureTypes.toList)) := by
  intro traces
  have left := announce.packed_observe 0 false capture rfl announceTyped ambient (env false) (fun _ => rfl)
  have right := wire.packed_observe 0 false capture rfl wireTyped ambient (env false) (fun _ => rfl)
  have traces' := congrArg₂ TraceLE left right ▸ traces
  have accepted := (announce.refinementAt?_iff_packedOutput wire 0 false).mpr traces'
  have rejected : announce.refinementAt? wire 0 false = false := by cbv
  simp [rejected] at accepted

private def cycleTarget := (elaborate (cycleOnFalse.compile 0) cycleOnFalse.exits capture).get (by decide)

private theorem cycleTyped : cycleTarget.HasType captureTypes (fun _ => packet) (fun _ => packet) :=
  check_sound cycleTarget captureTypes (fun _ => packet) (fun _ => packet) (by decide)

example : ¬ TraceLEWithSilence
    (region Program.primitive (extend ambient (packEnv 1 (env false)))
      ((FiniteCFG.packedExecutionRegion cycleTyped).packInputsDestructure captureTypes.toList))
    (region Program.primitive (extend ambient (packEnv 1 (env false)))
      ((FiniteCFG.packedExecutionRegion announceTyped).packInputsDestructure captureTypes.toList)) := by
  intro traces
  have left := cycleOnFalse.packed_observe 0 false capture rfl cycleTyped ambient (env false) (fun _ => rfl)
  have right := announce.packed_observe 0 false capture rfl announceTyped ambient (env false) (fun _ => rfl)
  have traces' := congrArg₂ TraceLEWithSilence left right ▸ traces
  have yes := (cycleOnFalse.refinementAtWithSilence?_iff_packedOutput announce 0 false).mpr traces'
  have no : cycleOnFalse.refinementAtWithSilence? announce 0 false = false := by cbv
  simp [no] at yes

end Packed

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Visible
