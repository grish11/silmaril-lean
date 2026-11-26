module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Thms

/-! # The same payload and live-outs at two distinct declared exits -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block br)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree out out_ret iterate_fixpoint Visible)
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Transfer region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)

private abbrev SortName := ULift.{1} Unit
private abbrev Reg := ULift.{1} Nat
private abbrev Key := ULift.{1} Nat
private abbrev Atom := ULift.{1} Nat
private abbrev Event (_ : Type) := Empty

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private instance : HasTy Empty (Ty SortName) := ⟨Empty.elim, Empty.elim⟩
private instance : HasEff Empty Bool := ⟨Empty.elim⟩
private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

private abbrev signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Empty

private instance : DecidableEq signature.Instr := fun f => Empty.elim f

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event signature.Instr where
  instructions :=
    { denote := fun f => Empty.elim f
      denotePure := fun f => Empty.elim f
      denote_pure := fun f => Empty.elim f }
  raw := Empty.elim
  compatible := fun f => Empty.elim f

private abbrev num : Ty SortName := .base ⟨()⟩
private abbrev choiceType : Ty SortName := .coprod num num
private def choiceName : Reg := ⟨0⟩
private def seedX : Reg := ⟨1⟩
private def seedY : Reg := ⟨2⟩
private def x : Reg := ⟨3⟩
private def y : Reg := ⟨4⟩
private def swappedX : Reg := ⟨5⟩
private def swappedY : Reg := ⟨6⟩
private def leftReply : Reg := ⟨7⟩
private def rightReply : Reg := ⟨8⟩
private def copyX : Reg := ⟨9⟩
private def copyY : Reg := ⟨10⟩
private def first : Key := ⟨10⟩
private def finish : Key := ⟨20⟩
private def leftExit : Option Key := some ⟨90⟩
private def rightExit : Option Key := some ⟨40⟩

private def returned (reply firstField secondField : Reg) : Val Reg :=
  .pair (.var reply) (.pair (.var firstField) (.pair (.var secondField) .unit))

private def firstBlock : Block Reg Key Empty :=
  ⟨[⟨x, [(none, .var seedX)]⟩, ⟨y, [(none, .var seedY)]⟩], .term (br finish)⟩

private def finishBlock : Block Reg Key Empty :=
  ⟨[⟨swappedX, [(some first, .var y)]⟩, ⟨swappedY, [(some first, .var x)]⟩],
    .let1 copyX (.val (.var swappedX)) (.let1 copyY (.val (.var swappedY))
      (.term (.case (.val (.var choiceName))
        leftReply (.br leftExit (returned leftReply swappedX swappedY))
        rightReply (.br rightExit (returned rightReply copyX copyY)))))⟩

private def graph : Graph Reg Key Empty :=
  ⟨.term (br first), [(first, firstBlock), (finish, finishBlock)]⟩

private def context : BoundCtx (Ty SortName) 3 := .snoc (.snoc (.snoc .nil num) num) choiceType

private def captures : Captures Reg context where
  names i := some ⟨i.val⟩
  distinct _ _ eq := Fin.ext (congrArg (fun name : Option Reg => (name.getD ⟨0⟩).down) eq)
  privateUnit _ eq := by nomatch eq

private abbrev ports : NamedFlat.Entry.Interface SortName Reg (Option Key) :=
  NamedFlat.Entry.Reverse.numberedInterface context [rightExit, leftExit] (fun _ => num)

-- The first exit reads the decoded φ fields. The other reads local copies
-- of the same two values, at different physical registers.
private def fields (key : Option Key) : List (Reg × Ty SortName) :=
  if key = leftExit then [(⟨12⟩, num), (⟨14⟩, num)] else [(⟨16⟩, num), (⟨17⟩, num)]
private abbrev registers := NamedFlat.Entry.Reverse.freshRegisters 3
private def pairPacket : Ty SortName := .product num (.product num .unit)
private def supportPacket : Ty SortName := .product num (.product num (.product choiceType .unit))
private def packet : Ty SortName := .product pairPacket supportPacket

private def inputs := [choiceName, seedX, seedY]
private def arrivals : CFG.Cyclic.Phi.GlobalSSA.Certificate Reg Key := [(first, [choiceName]), (finish, [choiceName])]

private def admitted : Admission signature ports fields captures :=
  (admit ports fields captures graph inputs arrivals (fun _ => packet)).get (by decide)

private def lowered : NamedFlat.Entry.Reverse.Lowered ports fields admitted.code :=
  (admitted.reverseChecked registers (fun i => some ⟨i.val⟩)).get (by decide)

private def recompiled : NamedFlat.Entry.LiveOut.Admission signature ports fields lowered.source :=
  (lowered.reAdmit admitted.internal).get (by decide)

example : CFG.Cyclic.Phi.OrderedExits.check graph [leftExit] inputs arrivals = false := by decide

-- The record shape is identical at both exits. Swap reads at just one exit.
example : (NamedFlat.Entry.Reverse.lowerChecked ports
    (fun k => if k = leftExit then (fields k).reverse else fields k)
    registers (fun i => some ⟨i.val⟩) admitted.code).isNone := by decide

private def record (chooseLeft : Bool) : Input context :=
  (((PUnit.unit, ⟨9⟩), ⟨7⟩), if chooseLeft then .inl ⟨13⟩ else .inr ⟨13⟩)

private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩
private def resultValue : Value Runtime := .pair (atom 13) (.pair (atom 9) (.pair (atom 7) .unit))
private def result (chooseLeft : Bool) : Transfer Runtime :=
  FiniteCFG.packedTreeOutput (if chooseLeft then 1 else 0, resultValue)

private abbrev runtimeModel := treeModel model.raw
private abbrev Pending := CFG.Cyclic.Phi.OrderedExits.Pending Reg Key (Value Runtime)
private abbrev step := CFG.Cyclic.Phi.OrderedExits.step runtimeModel graph

private def firstPending (chooseLeft : Bool) : Pending :=
  (none, some first, .unit, captures.store (record chooseLeft))

private def finishPending (chooseLeft : Bool) : Pending :=
  (some first, some finish, .unit, upd (upd (captures.store (record chooseLeft)) x (atom 7)) y (atom 9))

private def exitPending (chooseLeft : Bool) : Pending :=
  let store := upd (upd (finishPending chooseLeft).2.2.2 swappedX (atom 9)) swappedY (atom 7)
  let copies := upd (upd store copyX (atom 9)) copyY (atom 7)
  (some finish, if chooseLeft then leftExit else rightExit, resultValue,
    upd copies (if chooseLeft then leftReply else rightReply) (atom 13))

private theorem take_first (chooseLeft : Bool) :
    step (firstPending chooseLeft) = pure (.inr (finishPending chooseLeft)) := by
  unfold step firstPending
  rw [CFG.Cyclic.Phi.OrderedExits.step_internal _ _ _ _ _ _ (block := firstBlock) rfl]
  simp only [firstBlock, CFG.Cyclic.Phi.OrderedExits.execute, CFG.Body.exec, br, CFG.Term.exec, Val.eval, map_pure]
  rfl

private theorem take_finish (chooseLeft : Bool) :
    step (finishPending chooseLeft) = pure (.inr (exitPending chooseLeft)) := by
  unfold step finishPending
  rw [CFG.Cyclic.Phi.OrderedExits.step_internal _ _ _ _ _ _ (block := finishBlock) rfl]
  simp only [finishBlock, CFG.Cyclic.Phi.OrderedExits.execute, CFG.Body.exec, CFG.Term.exec,
    Op.eval, Val.eval, pure_bind]
  cases chooseLeft
  · erw [show runtimeModel.split (.inr (atom 13)) = pure (Sum.inr (atom 13)) from rfl]
    simp only [pure_bind, map_pure]
    rfl
  · erw [show runtimeModel.split (.inl (atom 13)) = pure (Sum.inl (atom 13)) from rfl]
    simp only [pure_bind, map_pure]
    rfl

private theorem take_exit (chooseLeft : Bool) :
    step (exitPending chooseLeft) =
      pure (.inl (if chooseLeft then leftExit else rightExit, resultValue)) := by
  cases chooseLeft <;> rfl

private theorem source_result (chooseLeft : Bool) :
    admitted.observe model (record chooseLeft) = pure (result chooseLeft) := by
  change (pure (firstPending chooseLeft) >>= iter step >>= _) = _
  rw [pure_bind, congrFun (iterate_fixpoint step) (firstPending chooseLeft), take_first, pure_bind]
  simp only [Sum.elim_inr]
  rw [congrFun (iterate_fixpoint step) (finishPending chooseLeft), take_finish, pure_bind]
  simp only [Sum.elim_inr]
  rw [congrFun (iterate_fixpoint step) (exitPending chooseLeft), take_exit, pure_bind]
  simp only [Sum.elim_inl, pure_bind]
  cases chooseLeft <;> rfl

/-- The actual RTL run returns by the declared exit index, for either
input arm with exactly the same old payload and ordered live-out values. -/
theorem emitted_result (chooseLeft : Bool) :
    NamedFlat.Entry.LiveOut.observe model ports fields lowered.source (record chooseLeft) =
      pure (result chooseLeft) :=
  (admitted.observe_reverse lowered model (record chooseLeft)).symm.trans (source_result chooseLeft)

theorem readmitted_result (chooseLeft : Bool) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue _ _ (record chooseLeft))) recompiled.program.code =
      pure (result chooseLeft) :=
  (admitted.observe_roundTrip lowered recompiled model (record chooseLeft) ambient).symm.trans
    (source_result chooseLeft)

theorem emitted_tags_distinct :
    NamedFlat.Entry.LiveOut.observe model ports fields lowered.source (record true) ≠
      NamedFlat.Entry.LiveOut.observe model ports fields lowered.source (record false) := by
  rw [emitted_result, emitted_result]
  intro eq
  have seen := congrArg out eq
  change out (Silmaril.Elgot.ITree.ret (result true)) =
    out (Silmaril.Elgot.ITree.ret (result false)) at seen
  rw [out_ret, out_ret] at seen
  have exits := Visible.ret.inj (Part.some_inj.mp seen)
  simp [result, FiniteCFG.packedTreeOutput, Region.packedExitValue] at exits

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Examples
