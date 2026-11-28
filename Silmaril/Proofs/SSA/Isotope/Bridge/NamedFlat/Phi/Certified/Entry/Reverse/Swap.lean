module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Reverse.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Thms

/-! # A predecessor-snapshot swap through the actual checked RTL lowerer -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.ReverseSwap

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Pending assign br ret)
open Silmaril.Elgot.ITree (Tree vis vis_bind resume resume_body)
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive Transfer region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree Compatible)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input)
open PureCapture (sourceObservation)
open PureCapture.Local

private abbrev SortName := ULift.{1} Unit
private abbrev Reg := ULift.{1} Nat
private abbrev Key := ULift.{1} Nat
private abbrev Atom := ULift.{1} Nat

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

private inductive Opcode
  | tick
  deriving DecidableEq

private inductive Event : Type → Type
  | tick (left right : Nat) : Event Nat

private abbrev num : Ty SortName := .base ⟨()⟩
private instance : HasTy Opcode (Ty SortName) := ⟨fun _ => .product num num, fun _ => num⟩
private instance : HasEff Opcode Bool := ⟨fun _ => true⟩

private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩

private def instr : Primitive Event Opcode Runtime
  | .tick, .pair (.atom left) (.atom right) => vis (.tick left.2.down right.2.down) fun reply => pure (atom reply)
  | _, _ => Silmaril.Elgot.ITree.diverge

private def typed : Silmaril.Isotope.Semantics.InstructionModel
    (Ty.denote (AtomValues.carrier (κ := SortName))) Opcode (ModelTree Event) where
  eval
    | .tick, (left, right) => vis (.tick left.down right.down) fun reply => pure ⟨reply⟩

private theorem compatible : Compatible (κ' := SortName) typed instr := by
  intro op args
  cases op
  obtain ⟨left, right⟩ := args
  change (vis (.tick left.down right.down) fun reply => pure (atom reply)) =
    ((vis (.tick left.down right.down) (fun reply => pure ⟨reply⟩) : Tree Event Atom) >>=
      fun reply => pure (atom reply.down))
  simp only [vis_bind, pure_bind]

private def signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Opcode

private instance : DecidableEq signature.Instr := inferInstanceAs (DecidableEq Opcode)

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event signature.Instr where
  instructions :=
    { denote := typed.eval
      denotePure := fun _ hf => Bool.noConfusion hf
      denote_pure := fun _ hf => Bool.noConfusion hf }
  raw := instr
  compatible := compatible

private def seedX : Reg := ⟨0⟩
private def seedY : Reg := ⟨1⟩
private def x : Reg := ⟨2⟩
private def y : Reg := ⟨3⟩
private def swappedX : Reg := ⟨4⟩
private def swappedY : Reg := ⟨5⟩
private def reply : Reg := ⟨6⟩
private def first : Key := ⟨10⟩
private def finish : Key := ⟨20⟩

private def firstBlock : Block Reg Key Opcode :=
  ⟨[⟨x, [(none, .var seedX)]⟩, ⟨y, [(none, .var seedY)]⟩], .term (br finish)⟩

private def finishBlock : Block Reg Key Opcode :=
  ⟨[⟨swappedX, [(some first, .var y)]⟩, ⟨swappedY, [(some first, .var x)]⟩],
    .let1 reply (.app .tick (.pair (.var swappedX) (.var swappedY)))
      (.term (ret (.pair (.var reply) (.pair (.var swappedX) (.pair (.var swappedY) .unit)))))⟩

private def graph : Graph Reg Key Opcode :=
  ⟨.term (br first), [(first, firstBlock), (finish, finishBlock)]⟩

private def context : BoundCtx (Ty SortName) 2 := .snoc (.snoc .nil num) num

private def captures : Captures Reg context where
  names i := some ⟨i.val⟩
  distinct _ _ eq := Fin.ext (congrArg (fun name : Option Reg => (name.getD ⟨0⟩).down) eq)
  privateUnit _ eq := by nomatch eq

private def ports : ReverseInterface SortName Reg Key 2 where
  inputs i := ⟨i.val⟩
  distinct _ _ eq := Fin.ext (congrArg ULift.down eq)
  exit := ⟨99⟩
  payload := num
  liveOut := [(⟨9⟩, num), (⟨11⟩, num)]

private def registers : NamedFlat.Entry.Reverse.Registers Reg := ⟨⟨2⟩, fun i => ⟨3 + i⟩⟩

private def pairPacket : Ty SortName := .product num (.product num .unit)
private def packet : Ty SortName := .product pairPacket pairPacket

private def admitted : Admitted signature captures Key ports.external :=
  .ofAdmission ((Certified.admit graph [seedX, seedY] [(first, []), (finish, [])]
    captures.names context (fun _ => packet) ports.external).get (by decide))

private def lowered : ReverseLowered ports admitted :=
  (admitted.reverseChecked ports registers (fun i => ⟨i.val⟩)).get (by decide)

private def recompiled : NamedFlat.Entry.LiveOut.Admission signature (ports.named context)
    (fun _ => ports.liveOut) lowered.source :=
  (NamedFlat.Entry.LiveOut.admit (P := signature) (ports.named context) (fun _ => ports.liveOut)
    lowered.source (fun _ => .product packet pairPacket)).get (by decide)

private def record : Input context := ((PUnit.unit, ⟨9⟩), ⟨7⟩)

private def result (reply : Nat) : Transfer Runtime :=
  FiniteCFG.packedTreeOutput (0, .pair (atom reply) (.pair (atom 9) (.pair (atom 7) .unit)))

-- The live-out fields have the same types in either order, so this
-- rejection checks the written reads in the return record.
example : (admitted.reverseChecked { ports with liveOut := ports.liveOut.reverse }
    registers (fun i => ⟨i.val⟩)).isNone := by decide

private abbrev State := Pending Reg Key (Value Runtime)
private def inputStore := captures.store record
private def predecessorStore := upd (upd inputStore x (atom 7)) y (atom 9)
private def swappedStore := upd (upd predecessorStore swappedX (atom 9)) swappedY (atom 7)

private def output (answer : Nat) : Value Runtime :=
  .pair (atom answer) (.pair (atom 9) (.pair (atom 7) .unit))

private theorem entry_step :
    entryTree instr graph inputStore = pure (.inr (.jump none first, inputStore)) := by
  simp [entryTree, graph, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br]

private theorem first_step :
    stepTree instr graph (.jump none first, inputStore) =
      pure (.inr (.jump (some first) finish, predecessorStore)) := by
  rw [step_jump _ _ _ _ _ (block := firstBlock) rfl]
  simp [firstBlock, assign, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br]
  rfl

private theorem finish_step :
    stepTree instr graph (.jump (some first) finish, predecessorStore) =
      vis (.tick 9 7) (fun answer =>
        pure (.inr (.returned (output answer), upd swappedStore reply (atom answer)))) := by
  rw [step_jump _ _ _ _ _ (block := finishBlock) rfl]
  have assigned : assign (treeModel instr) (some first) predecessorStore finishBlock.rows
      predecessorStore = swappedStore := rfl
  rw [assigned]
  simp [finishBlock, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
    treeModel, instr, swappedStore, upd, swappedX, swappedY, reply, output, ret, atom, vis_bind,
    ← bind_pure_comp]

private theorem resume_next (state : State) :
    resume (stepTree instr graph) (pure (.inr state)) =
      resume (stepTree instr graph) (stepTree instr graph state) := by
  rw [resume_body]
  simp [resume]

private theorem source_tree :
    admitted.observe model record = vis (.tick 9 7) (fun answer => pure (result answer)) := by
  change sourceObservation instr graph inputStore = _
  rw [sourceObservation_eq_resume, entry_step, resume_next, first_step, resume_next, finish_step]
  simp only [resume, vis_bind, pure_bind, Sum.elim_inr]
  congr 1
  funext answer
  rw [← resume_body, step_return]
  simp [resume, result, output, FiniteCFG.packedTreeOutput, Region.packedExitValue]
  rfl

/-- The request sees the swapped predecessor values. Its reply is the old
payload and the emitted RTL's two actual live-outs are in that same order. -/
theorem emitted_swap :
    NamedFlat.Entry.LiveOut.observe model (ports.named context) (fun _ => ports.liveOut) lowered.source record =
      vis (.tick 9 7) (fun answer => pure (result answer)) :=
  (admitted.observe_reverse lowered model record).symm.trans source_tree

theorem readmitted_swap (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue _ _ record)) recompiled.program.code =
      vis (.tick 9 7) (fun answer => pure (result answer)) :=
  (admitted.observe_reverse_roundTrip lowered recompiled model record ambient).symm.trans source_tree

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.ReverseSwap
