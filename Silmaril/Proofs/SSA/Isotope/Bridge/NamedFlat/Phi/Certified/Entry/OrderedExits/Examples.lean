module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.CaptureLiveness.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.SSA.LambdaRTL.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.UniformReadback.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Local.Thms

/-! # A checked φ split with two distinct declared exits -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block br)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree out out_ret iterate_fixpoint Visible ret_inj)
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Transfer region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open NamedFlat.Entry.Record (Input field)
open NamedFlat.Entry.Reverse.Straight (admitWithCaptures keepsEntryCapture keepsEntryCaptures checks encode_captures)
open NamedFlat.Entry.Reverse (Lowered Registers lower withLiveOut lower_attached_count
  elaborateAt_packetClosed observeAttached)
open NamedFlat.Entry (store store_at inputEnv)

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
  ⟨[⟨x, [(none, .var seedX)]⟩, ⟨y, [(none, .var seedY)]⟩],
    .term (.br (some finish) (.var x))⟩

private def finishBlock : Block Reg Key Empty :=
  ⟨[⟨swappedX, [(some first, .var y)]⟩, ⟨swappedY, [(some first, .var x)]⟩],
    .let1 copyX (.val (.var swappedX)) (.let1 copyY (.val (.var swappedY))
      (.term (.case (.val (.var choiceName))
        leftReply (.br leftExit (returned leftReply swappedX swappedY))
        rightReply (.br rightExit (returned rightReply copyX copyY)))))⟩

private def graph : Graph Reg Key Empty :=
  ⟨.term (br first), [(first, firstBlock), (finish, finishBlock)]⟩

private def commonContext {n : Nat} (older : BoundCtx (Ty SortName) n) :
    BoundCtx (Ty SortName) (n + 3) :=
  .snoc (.snoc (.snoc older num) num) choiceType

-- Both admissions use the same record, with numeric slots for the two
-- version-zero captures that the forwarding packet introduces.
private def context : BoundCtx (Ty SortName) 5 := commonContext (.snoc (.snoc .nil num) num)

private def numberedCaptures {n : Nat} (ctx : BoundCtx (Ty SortName) n) : Captures Reg ctx where
  names i := some ⟨i.val⟩
  distinct _ _ eq := Fin.ext (congrArg (fun name : Option Reg => (name.getD ⟨0⟩).down) eq)
  privateUnit _ eq := by nomatch eq

private abbrev captures := numberedCaptures context

private abbrev portsAt {n : Nat} (ctx : BoundCtx (Ty SortName) n) :
    NamedFlat.Entry.Interface SortName Reg (Option Key) :=
  NamedFlat.Entry.Reverse.numberedInterface ctx [rightExit, leftExit] (fun _ => num)

private abbrev ports := portsAt context

-- The first exit reads the decoded φ fields. The other reads local copies
-- of the same two values, at different physical registers.
private def fields (key : Option Key) : List (Reg × Ty SortName) :=
  if key = leftExit then [(⟨14⟩, num), (⟨16⟩, num)] else [(⟨18⟩, num), (⟨19⟩, num)]
private abbrev registers := NamedFlat.Entry.Reverse.freshRegisters 5
private def pairPacket : Ty SortName := .product num (.product num .unit)
private def supportPacket : Ty SortName := .product num (.product num (.product choiceType .unit))
private def packet : Ty SortName := .product pairPacket supportPacket

private def inputs := [choiceName, seedX, seedY]
private def arrivals : CFG.Cyclic.Phi.GlobalSSA.Certificate Reg Key := [(first, [choiceName]), (finish, [choiceName])]

private def admitAt {n : Nat} (ctx : BoundCtx (Ty SortName) n) :
    Option (Admission signature (portsAt ctx) fields (numberedCaptures ctx)) :=
  admit (portsAt ctx) fields (numberedCaptures ctx) graph inputs arrivals (fun _ => packet)

private def admitted : Admission signature ports fields captures :=
  (admitAt context).get (by decide)

private def lowered : NamedFlat.Entry.Reverse.Lowered ports fields admitted.code :=
  (admitted.reverseChecked registers (fun i => some ⟨i.val⟩)).get (by decide)

private def originalSlots : List (Fin ports.slots) := [1, 2, 0]

private theorem originalLayout (i : Fin _) :
    lowered.savedRegisters i = originalSlots.map (fun j => (⟨j.val⟩ : Reg)) := by decide +revert

private theorem originalKept : keepsEntryCaptures lowered originalSlots = true := by decide
private theorem originalChecked : checks lowered admitted.internal = true := by decide

private def recompiled : NamedFlat.Entry.LiveOut.Admission signature ports fields lowered.source :=
  admitWithCaptures lowered admitted.internal originalSlots originalLayout originalKept originalChecked

example : CFG.Cyclic.Phi.OrderedExits.check graph [leftExit] inputs arrivals = false := by decide

-- The record shape is identical at both exits. Swap reads at just one exit.
example : (NamedFlat.Entry.Reverse.lowerChecked ports
    (fun k => if k = leftExit then (fields k).reverse else fields k)
    registers (fun i => some ⟨i.val⟩) admitted.code).isNone := by decide

variable (olderX olderY : Atom)

private def record (chooseLeft : Bool) : Input context :=
  (((((PUnit.unit, olderY), olderX), ⟨9⟩), ⟨7⟩), if chooseLeft then .inl ⟨13⟩ else .inr ⟨13⟩)

private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩
private def resultValue : Value Runtime := .pair (atom 13) (.pair (atom 9) (.pair (atom 7) .unit))
private def result (chooseLeft : Bool) : Transfer Runtime :=
  FiniteCFG.packedTreeOutput (if chooseLeft then 1 else 0, resultValue)

private abbrev runtimeModel := treeModel model.raw
private abbrev Pending := CFG.Cyclic.Phi.OrderedExits.Pending Reg Key (Value Runtime)
private abbrev step := CFG.Cyclic.Phi.OrderedExits.step runtimeModel graph

private def firstPending (chooseLeft : Bool) : Pending :=
  (none, some first, .unit, captures.store (record olderX olderY chooseLeft))

private def finishPending (chooseLeft : Bool) : Pending :=
  let store := captures.store (record olderX olderY chooseLeft)
  (some first, some finish, atom 7, upd (upd store x (atom 7)) y (atom 9))

private def exitPending (chooseLeft : Bool) : Pending :=
  let store := upd (upd (finishPending olderX olderY chooseLeft).2.2.2 swappedX (atom 9)) swappedY (atom 7)
  let copies := upd (upd store copyX (atom 9)) copyY (atom 7)
  (some finish, if chooseLeft then leftExit else rightExit, resultValue,
    upd copies (if chooseLeft then leftReply else rightReply) (atom 13))

private theorem take_first (chooseLeft : Bool) :
    step (firstPending olderX olderY chooseLeft) = pure (.inr (finishPending olderX olderY chooseLeft)) := by
  unfold step firstPending
  rw [CFG.Cyclic.Phi.OrderedExits.step_internal _ _ _ _ _ _ (block := firstBlock) rfl]
  simp only [firstBlock, CFG.Cyclic.Phi.OrderedExits.execute, CFG.Body.exec, CFG.Term.exec, Val.eval, map_pure]
  rfl

private theorem take_finish (chooseLeft : Bool) :
    step (finishPending olderX olderY chooseLeft) = pure (.inr (exitPending olderX olderY chooseLeft)) := by
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
    step (exitPending olderX olderY chooseLeft) =
      pure (.inl (if chooseLeft then leftExit else rightExit, resultValue)) := by
  cases chooseLeft <;> rfl

private theorem source_result (chooseLeft : Bool) :
    admitted.observe model (record olderX olderY chooseLeft) = pure (result chooseLeft) := by
  change (pure (firstPending olderX olderY chooseLeft) >>= iter step >>= _) = _
  rw [pure_bind, congrFun (iterate_fixpoint step) (firstPending olderX olderY chooseLeft), take_first, pure_bind]
  simp only [Sum.elim_inr]
  rw [congrFun (iterate_fixpoint step) (finishPending olderX olderY chooseLeft), take_finish, pure_bind]
  simp only [Sum.elim_inr]
  rw [congrFun (iterate_fixpoint step) (exitPending olderX olderY chooseLeft), take_exit, pure_bind]
  simp only [Sum.elim_inl, pure_bind]
  cases chooseLeft <;> rfl

/-- The actual RTL run returns by the declared exit index, for either
input arm with exactly the same old payload and ordered live-out values. -/
theorem emitted_result (chooseLeft : Bool) :
    NamedFlat.Entry.LiveOut.observe model ports fields lowered.source (record olderX olderY chooseLeft) =
      pure (result chooseLeft) :=
  (admitted.observe_reverse lowered model (record olderX olderY chooseLeft)).symm.trans
    (source_result olderX olderY chooseLeft)

theorem readmitted_result (chooseLeft : Bool) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue _ _ (record olderX olderY chooseLeft))) recompiled.program.code =
      pure (result chooseLeft) :=
  (admitted.observe_roundTrip lowered recompiled model (record olderX olderY chooseLeft) ambient).symm.trans
    (source_result olderX olderY chooseLeft)

theorem emitted_tags_distinct :
    NamedFlat.Entry.LiveOut.observe model ports fields lowered.source (record olderX olderY true) ≠
      NamedFlat.Entry.LiveOut.observe model ports fields lowered.source (record olderX olderY false) := by
  rw [emitted_result, emitted_result]
  intro eq
  have seen := congrArg out eq
  change out (Silmaril.Elgot.ITree.ret (result true)) =
    out (Silmaril.Elgot.ITree.ret (result false)) at seen
  rw [out_ret, out_ret] at seen
  have exits := Visible.ret.inj (Part.some_inj.mp seen)
  simp [result, FiniteCFG.packedTreeOutput, Region.packedExitValue] at exits

private def splitLabel (key : Key) : Key := ⟨if key.down ≤ 90 then key.down else key.down + 1⟩

private def splitPlan : CFG.Cyclic.Phi.Split.Plan Reg Reg Key Key where
  register := Equiv.refl _
  label := ⟨splitLabel, by
    intro a b same
    have h := congrArg ULift.down same
    change (if a.down ≤ 90 then a.down else a.down + 1) =
      (if b.down ≤ 90 then b.down else b.down + 1) at h
    exact ULift.ext (by split at h <;> split at h <;> omega)⟩
  header := finish
  forward := ⟨91⟩
  fresh := by
    intro k eq
    have h := congrArg ULift.down eq
    change (if k.down ≤ 90 then k.down else k.down + 1) = 91 at h
    split at h <;> omega
  predecessor := some first

private def generated : GeneratedSplit splitPlan admitted :=
  (admitted.generateSplit splitPlan).get (by decide)

private abbrev splitAdmitted := generated.target

-- Global SSA inputs remain the original three names. The generated arrival
-- table adds the two operand reads only to the forwarder's arrival claim.
example : splitAdmitted.inputs = inputs ∧
    splitAdmitted.arrivals = (splitPlan.forward, [choiceName, y, x]) :: arrivals := by decide

private def baseContext := commonContext .nil
private def oneOlder := commonContext (.snoc .nil num)
private def wrongType := commonContext (.snoc (.snoc .nil num) .unit)

-- The original checks in all three smaller or mistyped interfaces. The
-- split requires both numeric version-zero slots in the common interface.
private def baseAdmission := (admitAt baseContext).get (by decide)
private def oneOlderAdmission := (admitAt oneOlder).get (by decide)
private def wrongTypeAdmission := (admitAt wrongType).get (by decide)

private def onlyY : Captures Reg oneOlder where
  names i := some ⟨if i.val = 3 then 4 else i.val⟩
  distinct i j eq := by
    apply Fin.ext
    have same := congrArg (fun name : Option Reg => (name.getD ⟨0⟩).down) eq
    change (if i.val = 3 then 4 else i.val) = (if j.val = 3 then 4 else j.val) at same
    split at same <;> split at same <;> omega
  privateUnit _ eq := by nomatch eq

private def onlyYAdmission : Admission signature (portsAt oneOlder) fields onlyY :=
  (admit (portsAt oneOlder) fields onlyY graph inputs arrivals (fun _ => packet)).get (by decide)

-- Run the actual typed elaborator even if the generator reports missing slots.
private def splitTypes {n : Nat} {ctx : BoundCtx (Ty SortName) n} {C : Captures Reg ctx}
    (a : Admission signature (portsAt ctx) fields C) : Bool :=
  (a.splitProfile splitPlan).any fun profile =>
    (NamedFlat.compileTyped (CFG.Cyclic.Phi.OrderedExits.lower (splitPlan.rewrite a.source))
      (portsAt ctx).exits (C.rename splitPlan.register).names ctx profile.blocks
      (NamedFlat.Entry.LiveOut.exitInterface (portsAt ctx) fields).external).isSome

example : ((baseAdmission.splitProfile splitPlan).map (·.extra)) =
    some [(some y, num), (some x, num)] := by decide
example : ((oneOlderAdmission.splitProfile splitPlan).map (·.extra)) =
    some [(some y, num)] := by decide
example : ((onlyYAdmission.splitProfile splitPlan).map (·.extra)) =
    some [(some x, num)] := by decide
example : ((wrongTypeAdmission.splitProfile splitPlan).map (·.movedSlots)) =
    some [(⟨4, by decide⟩, num), (⟨3, by decide⟩, num)] := by decide

example : (baseAdmission.generateSplit splitPlan).isNone ∧
    (oneOlderAdmission.generateSplit splitPlan).isNone ∧
    (onlyYAdmission.generateSplit splitPlan).isNone ∧
    (wrongTypeAdmission.generateSplit splitPlan).isNone := by decide

example : splitTypes baseAdmission = false ∧ splitTypes oneOlderAdmission = false ∧
    splitTypes onlyYAdmission = false ∧ splitTypes wrongTypeAdmission = false := by decide

private def originalSeed : ReverseSeed admitted :=
  ⟨registers, fun i => some ⟨i.val⟩, lowered, (Option.some_get _).symm⟩

private def splitRegisters : Registers Reg := (generated.relocatedRegisters originalSeed).get (by decide)

private abbrev RTL := CFG Reg (Option Key) signature.Instr

private def splitLabels (i : Fin 3) : Option Key := some ⟨i.val⟩

private def emitSplit (allocation : Registers Reg) : Option RTL :=
  lower allocation ports.names splitLabels (fun i => ports.exits[i]) splitAdmitted.code

private def splitRTL : Lowered ports fields splitAdmitted.code :=
  (generated.reverseRelocated originalSeed splitLabels).get (by decide)

private theorem splitInferred : generated.relocatedRegisters originalSeed = some splitRegisters :=
  (Option.some_get _).symm

private theorem splitAccepted : generated.reverseRelocated originalSeed splitLabels = some splitRTL :=
  (Option.some_get _).symm

private theorem splitRequests : generated.relocationDemands originalSeed =
    some [(12, ⟨14⟩), (14, ⟨16⟩), (16, ⟨18⟩), (17, ⟨19⟩)] := by decide

example : Relocation.Valid 5 registers.parameter (Relocation.writtenRegisters originalSeed.output.source)
    [(12, ⟨14⟩), (14, ⟨16⟩), (16, ⟨18⟩), (17, ⟨19⟩)] splitRegisters := by
  obtain ⟨_, requests, valid⟩ := generated.relocatedRegisters_valid originalSeed splitInferred
  rw [splitRequests] at requests
  cases Option.some.inj requests
  exact valid

example : emitSplit splitRegisters = some splitRTL.source ∧
    NamedFlat.elaborateAt (withLiveOut fields splitRTL.source) ports.exits ports.names _ splitRTL.count =
      some splitAdmitted.code := by
  obtain ⟨allocation, inferred, emitted, readback⟩ :=
    generated.reverseRelocated_spec originalSeed splitLabels splitAccepted
  have same := Option.some.inj (inferred.symm.trans splitInferred)
  exact ⟨same ▸ emitted, readback⟩

-- The original reverse allocation was accepted before the split. The
-- generated packet puts the live-out binders at different local depths.
example : (splitAdmitted.reverseChecked registers splitLabels).isNone := by decide

-- Swapping the two numeric left-exit registers in the relocated allocation
-- leaves a scoped, well-typed table but changes exactly that live-out readback.
private def swappedRegisters : Registers Reg :=
  { splitRegisters with localAt := fun i =>
      let name := splitRegisters.localAt i
      if name = ⟨14⟩ then ⟨16⟩ else if name = ⟨16⟩ then ⟨14⟩ else name }

example : (generated.relocationDemands originalSeed).any (Relocation.satisfies swappedRegisters) =
    false := by decide

private def swappedSource : RTL := (emitSplit swappedRegisters).get (by decide)
private theorem swappedEmitted : emitSplit swappedRegisters = some swappedSource := (Option.some_get _).symm
private def swappedAttached : RTL := withLiveOut (P := signature) fields swappedSource
private theorem swappedCount : swappedAttached.blocks.length = 3 :=
  lower_attached_count (I := ports) fields swappedEmitted

private def swappedRead := NamedFlat.elaborateAt swappedAttached ports.exits ports.names 3 swappedCount
private def swappedCode := swappedRead.get (by decide)

private theorem swappedScoped : swappedRead = some swappedCode := (Option.some_get _).symm

example : CFG.Cyclic.RoundTrip.PacketClosed swappedAttached :=
  elaborateAt_packetClosed _ _ _ swappedCount swappedScoped

example : swappedCode.HasType ports.context splitAdmitted.internal
    (NamedFlat.Entry.LiveOut.exitInterface ports fields).external :=
  NamedFlat.check_sound swappedCode ports.context splitAdmitted.internal _ (by decide)

private theorem swappedLastBlock : swappedCode.block 2 ≠ splitAdmitted.code.block (2 : Fin 3) := by
  let left : LambdaSSA.Flat signature.Instr 5 6 := swappedCode.block 2
  let right : LambdaSSA.Flat signature.Instr 5 6 := splitAdmitted.code.block (2 : Fin 3)
  let equality := NamedFlat.Entry.Reverse.instDecidableEqFlat left right
  exact @of_decide_eq_true (left ≠ right) (@instDecidableNot _ equality) rfl

example : swappedCode.entry = splitAdmitted.code.entry ∧
    swappedCode.block 0 = splitAdmitted.code.block (0 : Fin 3) ∧
    swappedCode.block 1 = splitAdmitted.code.block (1 : Fin 3) := ⟨rfl, rfl, rfl⟩

example : (splitAdmitted.reverseChecked swappedRegisters splitLabels).isSome = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have exactTable := (generated.reverseChecked_iff_readback swappedRegisters splitLabels swappedEmitted).mp accepted
  exact swappedLastBlock (congrArg (fun code => code.block (2 : Fin 3))
    (Option.some.inj (swappedScoped.symm.trans exactTable)))

private def splitSlots : List (Fin ports.slots) := [1, 2, 4, 3, 0]

private theorem splitLayout (i : Fin _) :
    splitRTL.savedRegisters i = splitSlots.map (fun j => (⟨j.val⟩ : Reg)) := by decide +revert

private theorem splitKept : keepsEntryCaptures splitRTL splitSlots = true := by decide
private theorem splitChecked : checks splitRTL splitAdmitted.internal = true := by decide

private def splitRecompiled : NamedFlat.Entry.LiveOut.Admission signature ports fields splitRTL.source :=
  admitWithCaptures splitRTL splitAdmitted.internal splitSlots splitLayout splitKept splitChecked

private abbrev Jump := CFG.Cyclic.Transfer Reg (Option Key) (Value Runtime)

private def entryStore (input : Input context) : Reg → Value Runtime :=
  store ports.names context input

/-- An actual boundary returned by the emitted entry or a finite prefix
of successful internal steps in this pure fixture. -/
private inductive Reached (g : RTL) (input : Input context) : Jump → Prop
  | entry {p} : CFG.Cyclic.enter runtimeModel g (entryStore input) = pure p → Reached g input p
  | step {p q} : Reached g input p →
      CFG.Cyclic.step runtimeModel g.blocks p = pure (.inr q) → Reached g input q

private theorem body_keeps_slot {A : Type 1} (body : CFG.Body Reg (Option Key) signature.Instr)
    (initial : Reg → Value Runtime) (name : Reg) (unassigned : name ∉ body.toRegion.bound)
    (send : Jump → A) (read : A → Value Runtime) (reads : ∀ p, read (send p) = p.2.2 name)
    (outgoing : A)
    (ran : body.exec runtimeModel (fun k v s => pure (send (k, v, s))) initial = pure outgoing) :
    read outgoing = initial name := by
  let exec := body.exec runtimeModel (fun k v s => pure (send (k, v, s))) initial
  have frame : (exec >>= fun p => pure (read p)) = (exec >>= fun _ => pure (initial name)) := by
    simp only [exec, CFG.Body.exec_eq_evalRTL, bind_assoc, pure_bind]
    apply Region.evalRTL_frame
    intro label value final agrees
    rw [reads]
    change pure (final name) = pure (initial name)
    rw [agrees name unassigned]
  rw [show exec = pure outgoing from ran, pure_bind, pure_bind] at frame
  exact ret_inj.mp frame

-- The implicit block-parameter writes are separate from the checked
-- nonassignment of the attached bodies.
private def paramsDisjoint (g : RTL) (slots : List (Fin ports.slots)) : Prop :=
  ∀ item ∈ g.blocks, ∀ i ∈ slots, (⟨i.val⟩ : Reg) ≠ item.2.param

private theorem agrees_at_reached {blocks : Nat} {liveOuts : Option Key → List (Reg × Ty SortName)}
    {code : FiniteCFG signature.Instr blocks ports.exits.length ports.slots}
    (a : Lowered ports liveOuts code) (slots : List (Fin ports.slots))
    (kept : keepsEntryCaptures a slots = true)
    (params : paramsDisjoint (withLiveOut liveOuts a.source) slots)
    (input : Input context) {p : Jump} (reached : Reached (withLiveOut liveOuts a.source) input p) :
    ∀ i ∈ slots, p.2.2 ⟨i.val⟩ = inputEnv context input i.val := by
  intro i member
  have unassigned := List.all_eq_true.mp kept i member
  simp only [keepsEntryCapture, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at unassigned
  induction reached with
  | @entry p ran =>
    have frame := body_keeps_slot _ _ ⟨i.val⟩ unassigned.1 id (fun p => p.2.2 ⟨i.val⟩)
      (fun _ => rfl) p ran
    exact frame.trans (store_at ports.names ports.distinct context input i)
  | @step p q before ran ih =>
    cases found : @List.lookup _ _ instBEqOfDecidableEq p.1
        (withLiveOut (P := signature) liveOuts a.source).blocks with
    | none =>
      simp only [CFG.Cyclic.step, found] at ran
      have impossible : (.inl p : Jump ⊕ Jump) = .inr q := ret_inj.mp ran
      cases impossible
    | some block =>
      have present : (p.1, block) ∈ (withLiveOut (P := signature) liveOuts a.source).blocks := by
        let : BEq (Option Key) := instBEqOfDecidableEq
        obtain ⟨_, _, list, _⟩ := List.lookup_eq_some_iff.mp found
        simp [list]
      simp only [CFG.Cyclic.step, found] at ran
      have frame := body_keeps_slot block.body (upd p.2.2 block.param p.2.1) ⟨i.val⟩
        (unassigned.2 _ present) (Sum.inr : Jump → Jump ⊕ Jump)
        (Sum.elim (fun p : Jump => p.2.2 ⟨i.val⟩) (fun p : Jump => p.2.2 ⟨i.val⟩))
        (fun _ => rfl) (.inr q) ran
      exact frame.trans (by simpa only [upd, ite_eq_right (params _ present i member)] using ih)

private theorem encodes_reached {blocks : Nat}
    {code : FiniteCFG signature.Instr blocks ports.exits.length ports.slots}
    (a : Lowered ports fields code) (slots : List (Fin ports.slots))
    (kept : keepsEntryCaptures a slots = true)
    (params : paramsDisjoint (withLiveOut fields a.source) slots)
    (input : Input context) {p : Jump} (reached : Reached (withLiveOut fields a.source) input p)
    (route : CFG.Cyclic.Versioning.destinations (withLiveOut fields a.source) p.1 =
      some (slots.map fun i => (⟨i.val⟩ : Reg))) :
    CFG.Cyclic.Versioning.encode runtimeModel (withLiveOut fields a.source) p =
      (p.1, .pair p.2.1 (slots.foldr (fun i tail => .pair (inputEnv context input i.val) tail) .unit)) :=
  encode_captures a model slots input p route (agrees_at_reached a slots kept params input reached)

private theorem originalParams : paramsDisjoint (withLiveOut fields lowered.source) originalSlots := by
  unfold paramsDisjoint
  decide
private theorem splitParams : paramsDisjoint (withLiveOut fields splitRTL.source) splitSlots := by
  unfold paramsDisjoint
  decide

private theorem originalRoute (i : Fin 2) :
    CFG.Cyclic.Versioning.destinations (withLiveOut fields lowered.source) (some ⟨i.val⟩) =
      some (originalSlots.map fun j => (⟨j.val⟩ : Reg)) := by decide +revert

private theorem splitRoute (i : Fin 3) :
    CFG.Cyclic.Versioning.destinations (withLiveOut fields splitRTL.source) (some ⟨i.val⟩) =
      some (splitSlots.map fun j => (⟨j.val⟩ : Reg)) := by decide +revert

-- Exercise the explicit agreement at the actual emitted entry on both sides.
example (input : Input context) :
    let g := withLiveOut (P := signature) fields lowered.source
    ∃ p : Jump, CFG.Cyclic.enter runtimeModel g (entryStore input) = pure p ∧
      CFG.Cyclic.Versioning.encode runtimeModel g p =
        (p.1, .pair p.2.1 (originalSlots.foldr (fun i tail => .pair (inputEnv context input i.val) tail) .unit)) := by
  have ran : ∃ p : Jump, CFG.Cyclic.enter runtimeModel (withLiveOut fields lowered.source) (entryStore input) =
      pure p ∧ p.1 = some ⟨0⟩ := ⟨_, rfl, rfl⟩
  obtain ⟨p, ran, label⟩ := ran
  exact ⟨p, ran, encodes_reached lowered originalSlots originalKept originalParams input (.entry ran)
    (by rw [label]; exact originalRoute 0)⟩

example (input : Input context) :
    let g := withLiveOut (P := signature) fields splitRTL.source
    ∃ p : Jump, CFG.Cyclic.enter runtimeModel g (entryStore input) = pure p ∧
      CFG.Cyclic.Versioning.encode runtimeModel g p =
        (p.1, .pair p.2.1 (splitSlots.foldr (fun i tail => .pair (inputEnv context input i.val) tail) .unit)) := by
  have ran : ∃ p : Jump, CFG.Cyclic.enter runtimeModel (withLiveOut fields splitRTL.source) (entryStore input) =
      pure p ∧ p.1 = some ⟨1⟩ := ⟨_, rfl, rfl⟩
  obtain ⟨p, ran, label⟩ := ran
  exact ⟨p, ran, encodes_reached splitRTL splitSlots splitKept splitParams input (.entry ran)
    (by rw [label]; exact splitRoute 1)⟩

example :
    let exitPlan := { splitPlan with header := ⟨90⟩, predecessor := some finish }
    exitPlan.hasEdge graph = true ∧ checkSplit exitPlan graph (exitPlan.rewrite graph) = false := by decide

/-- The split path runs the actual emitted RTL. Both choices keep their
exit numbers and the crosswise copy yields the ordered live-outs 9, 7. -/
theorem split_emitted_result (chooseLeft : Bool) :
    NamedFlat.Entry.LiveOut.observe model ports fields splitRTL.source (record olderX olderY chooseLeft) =
      pure (result chooseLeft) :=
  (generated.reverse_eq lowered splitRTL model (record olderX olderY chooseLeft)).symm.trans (emitted_result olderX olderY chooseLeft)

theorem split_readmitted_result (chooseLeft : Bool) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue _ _ (record olderX olderY chooseLeft))) splitRecompiled.program.code =
      pure (result chooseLeft) :=
  (generated.roundTrip_eq_of_uniformReadback lowered splitRTL originalSlots splitSlots
    originalLayout splitLayout originalKept splitKept originalChecked splitChecked
    model (record olderX olderY chooseLeft) ambient).symm.trans
      (readmitted_result olderX olderY chooseLeft ambient)

private theorem movedSlots : admitted.movedCaptureSlots splitPlan = [4, 3] := by decide

-- Both slots really occur free at version zero in the typed split entry.
-- Neither slot is free in the original entry.
example : splitAdmitted.entryUsesSlot 3 ∧ splitAdmitted.entryUsesSlot 4 := by decide

example : ¬ admitted.entryUsesSlot 3 ∧ ¬ admitted.entryUsesSlot 4 :=
  ⟨admitted.movedCaptureSlot_unused splitPlan (by rw [movedSlots]; decide),
    admitted.movedCaptureSlot_unused splitPlan (by rw [movedSlots]; decide)⟩

private theorem agreesOutsideMoved (newX newY : Atom) (chooseLeft : Bool)
    (i : Fin ports.slots) (kept : i ∉ admitted.movedCaptureSlots splitPlan) :
    field context (record olderX olderY chooseLeft) i =
      field context (record newX newY chooseLeft) i := by
  obtain ⟨i, bound⟩ := i
  change i < 5 at bound
  have slots : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases slots with rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · exact (kept (by
      change (3 : Fin ports.slots) ∈ admitted.movedCaptureSlots splitPlan
      rw [movedSlots]
      decide)).elim
  · exact (kept (by
      change (4 : Fin ports.slots) ∈ admitted.movedCaptureSlots splitPlan
      rw [movedSlots]
      decide)).elim

theorem split_packed_capture_irrelevant (newX newY : Atom) (chooseLeft : Bool) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue _ _ (record olderX olderY chooseLeft)))
        (Program.ofCFGEntry splitAdmitted.typed).code =
      region model.raw (extend ambient (encodeValue _ _ (record newX newY chooseLeft)))
        (Program.ofCFGEntry splitAdmitted.typed).code :=
  generated.packed_eq_of_movedCaptures model _ _ ambient
    (agreesOutsideMoved olderX olderY newX newY chooseLeft)

/-- Vary both required numeric captures with the same supplied live fields.
The witnessed equality is between runs of the actual emitted mutable graph. -/
theorem split_emitted_capture_irrelevant (newX newY : Atom) (chooseLeft : Bool) :
    NamedFlat.Entry.LiveOut.observe model ports fields splitRTL.source (record olderX olderY chooseLeft) =
      NamedFlat.Entry.LiveOut.observe model ports fields splitRTL.source (record newX newY chooseLeft) :=
  generated.reverse_eq_of_movedCaptures splitRTL model _ _
    (agreesOutsideMoved olderX olderY newX newY chooseLeft)

theorem split_readmitted_capture_irrelevant (newX newY : Atom) (chooseLeft : Bool) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue _ _ (record olderX olderY chooseLeft))) splitRecompiled.program.code =
      region model.raw (extend ambient (encodeValue _ _ (record newX newY chooseLeft))) splitRecompiled.program.code :=
  generated.roundTrip_eq_of_movedCaptures splitRTL splitRecompiled model _ _ ambient
    (agreesOutsideMoved olderX olderY newX newY chooseLeft)

section BranchingConflict

private def returnOne (name : Reg) : Val Reg :=
  .pair (.var name) (.pair (.var name) .unit)

-- The entry's left arm exits at local depth eight. Its right arm enters
-- the internal edge split below. Unit lets set the depth without adding
-- any version-zero reads or changing the branch.
private def entryPrefix : Nat → CFG.Body Reg (Option Key) Empty → CFG.Body Reg (Option Key) Empty
  | 0, body => body
  | n + 1, body => .let1 ⟨100 + n⟩ (.val .unit) (entryPrefix n body)

private def branchingGraph : Graph Reg Key Empty :=
  ⟨entryPrefix 8 (.term (.case (.val (.var choiceName))
    leftReply (.br leftExit (returnOne leftReply)) rightReply (br first))),
    [(first, ⟨[⟨x, [(none, .var seedX)]⟩], .term (br finish)⟩),
     (finish, ⟨[⟨swappedX, [(some first, .var x)]⟩], .term (.br rightExit (returnOne swappedX))⟩)]⟩

private def branchingFields (key : Option Key) : List (Reg × Ty SortName) :=
  [(if key = leftExit then ⟨14⟩ else ⟨12⟩, num)]

private def branching : Admission signature ports branchingFields captures :=
  (admit ports branchingFields captures branchingGraph [choiceName, seedX]
    [(first, []), (finish, [])]
    (fun _ => .product (.product num .unit) (.product choiceType (.product num .unit)))).get (by decide)

private def branchingLowered : Lowered ports branchingFields branching.code :=
  (branching.reverseChecked registers (fun i => some ⟨i.val⟩)).get (by decide)

private def branchingSeed : ReverseSeed branching :=
  ⟨registers, fun i => some ⟨i.val⟩, branchingLowered, (Option.some_get _).symm⟩

private def branchingSplit : GeneratedSplit splitPlan branching :=
  (branching.generateSplit splitPlan).get (by decide)

example : Relocation.demands registers.parameter
    (fun i : Fin ports.exits.length => (branchingFields ports.exits[i]).map Prod.fst)
    branching.code = some [(8, ⟨14⟩), (6, ⟨12⟩)] := rfl

private def branchingRequests : Relocation.DemandTable.{0} :=
  ⟨[(8, ⟨14⟩)], [[], [], [(8, ⟨12⟩)]]⟩

example : Relocation.tableDemands registers.parameter
    (fun i : Fin ports.exits.length => (branchingFields ports.exits[i]).map Prod.fst)
    branchingSplit.target.code = some branchingRequests := rfl

private theorem branchingRequests_found :
    branchingSplit.relocationDemands branchingSeed = some branchingRequests.all := by decide

-- Each body can allocate its requests with the same parameter and freshness
-- policy if considered separately.
example : ∀ requests ∈ branchingRequests.entry :: branchingRequests.blocks,
    ∃ allocation, Relocation.Valid 5 registers.parameter
      (Relocation.writtenRegisters branchingLowered.source) requests allocation := by
  intro requests member
  apply (Relocation.infer_isSome_iff_valid ..).mp
  simp only [branchingRequests, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

private theorem branching_global_conflict :
    ¬ Relocation.Constraints 5 registers.parameter branchingRequests.all := by
  intro valid
  have left : ((8, ⟨14⟩) : Relocation.Demand.{0}) ∈ branchingRequests.all := by
    exact List.mem_cons_self
  have right : ((8, ⟨12⟩) : Relocation.Demand.{0}) ∈ branchingRequests.all := by
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have same := valid.oneNamePerDepth _ left _ right rfl
  exact (by decide : (⟨14⟩ : Reg) ≠ ⟨12⟩) same

example : ¬ ∃ allocation, Relocation.Valid 5 registers.parameter
    (Relocation.writtenRegisters branchingLowered.source) branchingRequests.all allocation :=
  fun ⟨_, valid⟩ => branching_global_conflict valid.constraints

example : (branchingSplit.relocatedRegisters branchingSeed).isSome = false :=
  Bool.eq_false_iff.mpr fun accepted =>
    branching_global_conflict ((branchingSplit.relocatedRegisters_isSome_iff branchingSeed branchingRequests_found).mp accepted)

private def branchingAllocation : Relocation.BodyAllocations.{0} 3 :=
  (branchingSplit.relocatedByBody branchingSeed).get (by decide)

example : branchingAllocation.entry.parameter = registers.parameter ∧
    branchingAllocation.entry.localAt 8 = ⟨14⟩ ∧
    branchingAllocation.localAt 2 8 = ⟨12⟩ := by decide

private def branchingLocal : Lowered ports branchingFields branchingSplit.target.code :=
  (branchingSplit.reverseRelocatedByBody branchingSeed splitLabels).get (by decide)

private theorem branchingLocalAccepted :
    branchingSplit.reverseRelocatedByBody branchingSeed splitLabels = some branchingLocal :=
  (Option.some_get _).symm

example : Function.Injective (SSA.FiniteSum.append splitLabels (fun i => ports.exits[i])) :=
  (branchingSplit.reverseRelocatedByBody_spec branchingSeed splitLabels branchingLocalAccepted).1

example : (branchingSplit.reverseRelocatedByBody branchingSeed (fun _ => some ⟨0⟩)).isNone := by decide
example : (branchingSplit.reverseRelocatedByBody branchingSeed (fun _ => leftExit)).isNone := by decide

-- The attached body sees only the incoming packet. Even if an earlier
-- body used the same register for a different local, changing the carried
-- store cannot affect the next label or argument (including live-outs).
theorem branchingLocal_step_store_independent (label : Option Key) (arg : Value Runtime)
    (left right : Reg → Value Runtime) :
    let attached := withLiveOut (P := signature) branchingFields branchingLocal.source
    Sum.map obs obs <$> CFG.Cyclic.step runtimeModel attached.blocks (label, arg, left) =
      Sum.map obs obs <$> CFG.Cyclic.step runtimeModel attached.blocks (label, arg, right) :=
  (CFG.Cyclic.RoundTrip.step_packetClosed_obs runtimeModel _ branchingLocal.closed left (label, arg, left)).trans
    (CFG.Cyclic.RoundTrip.step_packetClosed_obs runtimeModel _ branchingLocal.closed left (label, arg, right)).symm

private def branchingOriginalSlots : List (Fin ports.slots) := [0, 1]
private def branchingLocalSlots : List (Fin ports.slots) := [0, 1, 3]

private def branchingRecompiled : NamedFlat.Entry.LiveOut.Admission signature ports branchingFields
    branchingLowered.source :=
  admitWithCaptures branchingLowered branching.internal branchingOriginalSlots (by decide) (by decide) (by decide)

private def branchingLocalRecompiled : NamedFlat.Entry.LiveOut.Admission signature ports branchingFields
    branchingLocal.source :=
  admitWithCaptures branchingLocal branchingSplit.target.internal branchingLocalSlots
    (by decide) (by decide) (by decide)

/-- The actual mutable RTL preserves ordered exit observations for each supplied record. -/
theorem branchingLocal_emitted_eq (input : Input context) :
    NamedFlat.Entry.LiveOut.observe model ports branchingFields branchingLowered.source input =
      NamedFlat.Entry.LiveOut.observe model ports branchingFields branchingLocal.source input :=
  branchingSplit.reverse_eq branchingLowered branchingLocal model input

/-- Both actual RTL tables re-admit and agree at the same packed interface. -/
theorem branchingLocal_packed_eq (input : Input context) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue _ _ input)) branchingRecompiled.program.code =
      region model.raw (extend ambient (encodeValue _ _ input)) branchingLocalRecompiled.program.code :=
  branchingSplit.roundTrip_eq branchingLowered branchingLocal branchingRecompiled branchingLocalRecompiled
    model input ambient

private def branchingResult (chooseLeft : Bool) : Transfer Runtime :=
  let value := if chooseLeft then atom 13 else atom 7
  FiniteCFG.packedTreeOutput (if chooseLeft then 1 else 0, .pair value (.pair value .unit))

private theorem branching_source_result (chooseLeft : Bool) :
    branching.observe model (record olderX olderY chooseLeft) = pure (branchingResult chooseLeft) := by
  let σ := captures.store (record olderX olderY chooseLeft)
  let step := CFG.Cyclic.Phi.OrderedExits.step runtimeModel branchingGraph
  let val := if chooseLeft then atom 13 else atom 7
  let output := Value.pair val (.pair val .unit)
  let exit := if chooseLeft then leftExit else rightExit
  have leave (store : Reg → Value Runtime) (pred : Option Key) :
      iter step (pred, exit, output, store) = pure (exit, output) := by
    have external : step (pred, exit, output, store) = pure (.inl (exit, output)) := by
      cases chooseLeft <;> rfl
    rw [congrFun (iterate_fixpoint step) (pred, exit, output, store), external, pure_bind, Sum.elim_inl]
  let prefixStore := (List.range 8).foldr (fun i σ => upd σ ⟨100 + i⟩ .unit) σ
  let start : Pending := (none, some first, .unit, upd prefixStore rightReply (atom 13))
  let hop : Pending := (some first, some finish, .unit, upd start.2.2.2 x (atom 7))
  have firstStep : step start = pure (.inr hop) := by
    unfold step start
    rw [CFG.Cyclic.Phi.OrderedExits.step_internal _ _ _ _ _ _ rfl]
    simp only [CFG.Cyclic.Phi.OrderedExits.execute, CFG.Body.exec, CFG.Term.exec, br, map_pure]
    rfl
  have lastStep : step hop =
      pure (.inr (some finish, rightExit, .pair (atom 7) (.pair (atom 7) .unit),
        upd hop.2.2.2 swappedX (atom 7))) := by
    unfold step hop
    rw [CFG.Cyclic.Phi.OrderedExits.step_internal _ _ _ _ _ _ rfl]
    simp only [CFG.Cyclic.Phi.OrderedExits.execute, CFG.Body.exec, CFG.Term.exec, map_pure]
    rfl
  let entry := CFG.Cyclic.Phi.OrderedExits.execute runtimeModel none branchingGraph.entry σ
  change (entry >>= iter step >>= _) = _
  cases chooseLeft
  · have enter : entry = pure start := by
      simp only [entry, branchingGraph, entryPrefix, CFG.Cyclic.Phi.OrderedExits.execute,
        CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval, pure_bind, br]
      change (pure (Sum.inr (atom 13) : Value Runtime ⊕ Value Runtime) >>= _) = _
      rw [pure_bind]
      rfl
    rw [enter, pure_bind, congrFun (iterate_fixpoint step) start, firstStep, pure_bind, Sum.elim_inr,
      congrFun (iterate_fixpoint step) hop, lastStep, pure_bind, Sum.elim_inr]
    change (iter step (some finish, exit, output, _) >>= _) = _
    rw [leave, pure_bind]
    rfl
  · let done : Pending := (none, exit, output, upd prefixStore leftReply (atom 13))
    have enter : entry = pure done := by
      simp only [entry, branchingGraph, entryPrefix, CFG.Cyclic.Phi.OrderedExits.execute,
        CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval, pure_bind, br]
      change (pure (Sum.inl (atom 13) : Value Runtime ⊕ Value Runtime) >>= _) = _
      rw [pure_bind]
      rfl
    rw [enter, pure_bind]
    change (iter step (none, exit, output, _) >>= _) = _
    rw [leave, pure_bind]
    rfl

/-- The direct exit keeps tag 1 and payload 13. The arm that crosses the
forwarder keeps tag 0 and payload 7, with their declared live-out fields. -/
theorem branchingLocal_packed_result (chooseLeft : Bool) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue _ _ (record olderX olderY chooseLeft)))
      branchingLocalRecompiled.program.code = pure (branchingResult chooseLeft) :=
  (branchingSplit.roundTrip_eq branchingLowered branchingLocal branchingRecompiled branchingLocalRecompiled
    model (record olderX olderY chooseLeft) ambient).symm.trans
      ((branching.observe_roundTrip branchingLowered branchingRecompiled model
        (record olderX olderY chooseLeft) ambient).symm.trans
          (branching_source_result olderX olderY chooseLeft))

/-- Run the emitted RTL with its attached reads, through the new commuting
interface, on both branches of the same supplied typed input record. -/
theorem branchingLocal_attached_result (chooseLeft : Bool) :
    observeAttached model ports branchingFields branchingLocal.source (record olderX olderY chooseLeft) =
      pure (branchingResult chooseLeft) :=
  ((branchingSplit.bodyLocal_commutes branchingSeed splitLabels branchingLocalAccepted model
    (record olderX olderY chooseLeft) (fun _ => .unit)).2.1).symm.trans
      (branching_source_result olderX olderY chooseLeft)

example (input : Input context) (p : Jump)
    (reached : Reached (withLiveOut (P := signature) branchingFields branchingLocal.source) input p)
    (route : CFG.Cyclic.Versioning.destinations (withLiveOut branchingFields branchingLocal.source) p.1 =
      some (branchingLocalSlots.map fun i => (⟨i.val⟩ : Reg))) :
    let attached := withLiveOut branchingFields branchingLocal.source
    obs <$> iter (CFG.Cyclic.step runtimeModel attached.blocks) p =
      iter (CFG.Cyclic.stepSSA runtimeModel (CFG.Cyclic.Versioning.compile attached).blocks
        (store (fun i : Fin ports.slots => ((⟨i.val⟩ : Reg), 0)) context input))
        (p.1, .pair p.2.1 (branchingLocalSlots.foldr
          (fun i tail => .pair (inputEnv context input i.val) tail) .unit)) :=
  branchingLocal.resumeSaved_eq model branchingLocalSlots input p route
    (agrees_at_reached branchingLocal branchingLocalSlots (by decide) (by unfold paramsDisjoint; decide)
      input reached)

end BranchingConflict

-- The successful swap allocation still needs an exact label readback. The
-- same allocator emits with these labels, but all branches resolve to the
-- first internal block during elaboration.
private def collidingLabels (_ : Fin 3) : Option Key := some ⟨0⟩

private def collidingEmission :=
  lower splitRegisters ports.names collidingLabels (fun i => ports.exits[i]) splitAdmitted.code

private def collidingSource : RTL := collidingEmission.get (by decide)

private theorem collidingEmitted : collidingEmission = some collidingSource := (Option.some_get _).symm

example : NamedFlat.elaborateAt (withLiveOut fields collidingSource) ports.exits ports.names _
    (lower_attached_count (I := ports) fields collidingEmitted) ≠ some splitAdmitted.code := by
  intro readback
  have accepted := (generated.reverseRelocated_iff_readback originalSeed collidingLabels
    splitInferred collidingEmitted).mpr readback
  have rejected : (generated.reverseRelocated originalSeed collidingLabels).isSome = false := by decide
  rw [rejected] at accepted
  cases accepted

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Examples
