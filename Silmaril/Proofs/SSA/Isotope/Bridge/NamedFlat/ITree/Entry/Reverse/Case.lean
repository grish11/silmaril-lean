module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Institution.Thms

/-! # A typed sum packet selects distinct exits with identical payload types -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Case

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Acyclic
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (iterate_fixpoint)

private abbrev SortName := ULift.{1} Unit
private abbrev Reg := ULift.{1} Nat
private abbrev Label := ULift.{1} Nat
private abbrev Event (_ : Type) := Empty
private abbrev Atom := ULift.{1} Nat
private abbrev NoInstr := ULift.{1} Empty

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private instance : HasTy NoInstr (Ty SortName) := ⟨fun f => f.down.elim, fun f => f.down.elim⟩
private instance : HasEff NoInstr Bool := ⟨fun f => f.down.elim⟩

private def signature : FlatInstitution.Signature.{0, 1} SortName where
  Instr := NoInstr

private instance : DecidableEq signature.Instr := fun f => f.down.elim

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event signature.Instr where
  instructions :=
    { denote := fun f => f.down.elim
      denotePure := fun f => f.down.elim
      denote_pure := fun f => f.down.elim }
  raw := fun f => f.down.elim
  compatible := fun f => f.down.elim

private def num : Ty SortName := .base ⟨()⟩
private def choice : Ty SortName := .coprod num num
private def leftExit : Label := ⟨22⟩
private def rightExit : Label := ⟨11⟩

private abbrev ports : Interface SortName Reg Label :=
  numberedInterface (.snoc .nil choice) [leftExit, rightExit] (fun _ => num)
private def label (_ : Fin 1) : Label := ⟨7⟩
private def fields (_ : Label) : List (Reg × Ty SortName) := [(⟨2⟩, num)]

private def flat : FiniteCFG signature.Instr 1 ports.exits.length ports.slots where
  entry := .br 0 (.bv 0)
  block _ :=
    .case (.bv 0)
      (.br 1 (.pair (.bv 0) (.pair (.bv 0) .unit)))
      (.br 2 (.pair (.bv 0) (.pair (.bv 0) .unit)))

private theorem typed : flat.HasType ports.context (fun _ => choice)
    (LiveOut.exitInterface ports fields).external :=
  NamedFlat.check_sound flat ports.context (fun _ => choice) _ (by decide)

private def lowered : Lowered ports fields flat :=
  (lowerFresh label ports.context ports.exits ports.external fields flat).get (by decide)

-- The actual packet holds the sum argument and one saved sum capture.
example : ∀ i, lowered.savedRegisters i = [⟨0⟩] := by decide

private def profile := (lowered.synthesizeProfile (fun _ => choice)).get (by decide)

example : ∀ i, profile i = .product choice (.product choice .unit) := by decide

private def recompiled : LiveOut.Admission signature ports fields lowered.source :=
  Straight.admitWithCapture lowered (fun _ => choice) (by decide) 0
    (by decide) (by decide) (by decide)

example : (lowered.reAdmit (fun _ => choice)).isSome = true := by decide

private abbrev Input := Ty.denote (AtomValues.carrier (κ := SortName))
  (Region.packedInputType ports.context.toList)

private def input (right : Bool) (n : Nat) : Input :=
  (PUnit.unit, if right then .inr ⟨n⟩ else .inl ⟨n⟩)

private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩
private def value (right : Bool) (n : Nat) : Value Runtime :=
  if right then .inr (atom n) else .inl (atom n)

example (right : Bool) (n : Nat) :
    store ports.version.names ports.context (input right n) (⟨0⟩, 0) = value right n :=
  (Straight.capture_at_version_zero (context := ports.context) 0 (input right n)).trans
    (by cases right <;> rfl)

private def output (right : Bool) (n : Nat) : Transfer Runtime :=
  let packet := (atom n).pair ((atom n).pair .unit)
  (0, if right then .inr (.inl packet) else .inl packet)

example (n : Nat) : output false n ≠ output true n := by
  intro eq
  cases congrArg Prod.snd eq

private def table : List (Label × CFG.Block Reg Label signature.Instr) :=
  [(⟨7⟩, ⟨⟨1⟩, .term (.case (.val (.var ⟨1⟩))
    ⟨2⟩ (.br leftExit (.var ⟨2⟩)) ⟨2⟩ (.br rightExit (.var ⟨2⟩)))⟩)]

private theorem loweredTable : lowered.source.blocks = table := rfl

private def start (right : Bool) (n : Nat) : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
  (⟨7⟩, value right n, store ports.names ports.context (input right n))

-- The jump carries the actual supplied sum both as its argument and in
-- the saved record. The capture type and value use the same input slot.
example (right : Bool) (n : Nat) :
    CFG.Cyclic.Versioning.encode (treeModel model.raw) (withLiveOut (P := signature) fields lowered.source)
      (start right n) = (⟨7⟩, .pair (value right n) (.pair (value right n) .unit)) := by
  have route : CFG.Cyclic.Versioning.destinations
      (withLiveOut (P := signature) fields lowered.source) (⟨7⟩ : Label) = some [⟨0⟩] := by decide
  have agrees : (start right n).2.2 ⟨0⟩ = inputEnv ports.context (input right n) 0 := by
    cases right <;> rfl
  have packet := Straight.encode_capture lowered model 0 (input right n) (start right n) route agrees
  cases right <;> exact packet

private def done (right : Bool) (n : Nat) : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
  let σ := upd (start right n).2.2 ⟨1⟩ (value right n)
  (if right then rightExit else leftExit, atom n, upd σ ⟨2⟩ (atom n))

set_option maxRecDepth 2048 in
private theorem named_result_with_tail (source : CFG Reg Label signature.Instr)
    (tail : List (Label × CFG.Block Reg Label signature.Instr))
    (entry : source.entry = lowered.source.entry) (rows : source.blocks = table ++ tail)
    (leftExitFree : @List.lookup Label _ instBEqOfDecidableEq leftExit tail = none)
    (rightExitFree : @List.lookup Label _ instBEqOfDecidableEq rightExit tail = none)
    (right : Bool) (n : Nat) :
    LiveOut.observe (P := signature) model ports fields source (input right n) =
      pure (output right n) := by
  let step := CFG.Cyclic.step (treeModel model.raw) source.blocks
  have selectArm : step (start right n) = pure (.inr (done right n)) := by
    cases right <;>
      simp [step, rows, table, CFG.Cyclic.step, start, done, CFG.Body.exec, CFG.Term.exec,
        Op.eval, Val.eval, treeModel, value, upd]
  have exit : step (done right n) = pure (.inl (done right n)) := by
    have outside : @List.lookup Label _ instBEqOfDecidableEq (done right n).1 source.blocks = none := by
      rw [rows]
      cases right
      · exact leftExitFree
      · exact rightExitFree
    unfold step CFG.Cyclic.step
    rw [outside]
  have enter : CFG.Cyclic.run (treeModel model.raw) source
      (store ports.names ports.context (input right n)) = iter step (start right n) := by
    unfold CFG.Cyclic.run
    rw [entry]
    cases right <;> rfl
  change (CFG.Cyclic.run (treeModel model.raw) source
    (store ports.names ports.context (input right n)) >>= _) = _
  rw [enter, congrFun (iterate_fixpoint step) (start right n), selectArm, pure_bind]
  change (iter step (done right n) >>= _) = _
  rw [congrFun (iterate_fixpoint step) (done right n), exit, pure_bind]
  change (pure (done right n) >>= _) = _
  rw [pure_bind]
  cases right <;> rfl

private theorem named_result (right : Bool) (n : Nat) :
    LiveOut.observe (P := signature) model ports fields lowered.source (input right n) =
      pure (output right n) :=
  named_result_with_tail lowered.source [] rfl (by simpa using loweredTable) rfl rfl right n

private def packedInput (right : Bool) (n : Nat) : Value Runtime :=
  encodeValue (AtomValues.carrier (κ := SortName))
    (Region.packedInputType ports.context.toList) (input right n)

example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) (Program.ofCFGEntry typed).code =
      region model.raw (extend ambient (packedInput right n)) recompiled.program.code :=
  lowered.packed_roundTrip model typed recompiled (input right n) ambient

example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) recompiled.program.code =
      pure (output right n) :=
  (recompiled.packed_tree model (input right n) ambient).trans (named_result right n)

-- Both original exit tags and the projected binder value still depend
-- on the caller's supplied sum after the saved record is removed.
private def packetLocalCase : PacketLocal.Admission lowered :=
  PacketLocal.admit lowered (fun _ => choice) (by decide)

example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) packetLocalCase.program.code =
      pure (output right n) :=
  (packetLocalCase.packed_tree model (input right n) ambient).trans (named_result right n)

private theorem packetLocalCaseRank : packetLocalCase.acyclicCheck = true := by decide

-- The typed LetCase term is expanded from the actual admitted opt-in table.
-- Its two branches preserve the ordered exit tag and selected live-out.
example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    (packetLocalCase.letCaseTree model packetLocalCaseRank (input right n) >>= fun result =>
      pure (0, encodeValue (AtomValues.carrier (κ := SortName))
        (Region.packedExitType (List.ofFn (LiveOut.exitInterface ports fields).external)) result)) =
      pure (output right n) :=
  (packetLocalCase.letCase_observe model packetLocalCaseRank (input right n) ambient).trans (named_result right n)

/-- Keep the input and the two exits, with the dispatcher in the entry.
The left arm unpacks the same sum again and uses both binder depths. -/
private def entryOnly : FiniteCFG signature.Instr 0 ports.exits.length ports.slots where
  entry := .case (.bv 0)
    (.case (.bv 1)
      (.br 0 (.pair (.bv 0) (.pair (.bv 1) .unit)))
      (.br 0 (.pair (.bv 0) (.pair (.bv 1) .unit))))
    (.br 1 (.pair (.bv 0) (.pair (.bv 0) .unit)))
  block := Fin.elim0

private def entryLowered : Lowered ports fields entryOnly :=
  (lowerFresh Fin.elim0 ports.context ports.exits ports.external fields entryOnly).get (by decide)

private theorem entryTyped : entryOnly.HasType ports.context Fin.elim0
    (LiveOut.exitInterface ports fields).external :=
  NamedFlat.check_sound entryOnly ports.context Fin.elim0 _ (by decide)

-- All obligations concern the original source or the saved-register list.
private def entryAdmission : LiveOut.Admission signature ports fields entryLowered.source :=
  Straight.admit entryLowered Fin.elim0 (by decide) (by decide) (by decide)

private theorem entryShape : entryLowered.source =
    ⟨.term (.case (.val (.var ⟨0⟩)) ⟨2⟩
      (.case (.val (.var ⟨0⟩)) ⟨3⟩ (.br leftExit (.var ⟨3⟩))
        ⟨3⟩ (.br leftExit (.var ⟨3⟩)))
      ⟨2⟩ (.br rightExit (.var ⟨2⟩))), []⟩ := rfl

set_option maxRecDepth 2048 in
private theorem entry_named_result (right : Bool) (n : Nat) :
    LiveOut.observe (P := signature) model ports fields entryLowered.source (input right n) =
      pure (output right n) := by
  let m := treeModel model.raw
  let σ := store ports.names ports.context (input right n)
  let outer := upd σ ⟨2⟩ (atom n)
  let pending : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
    (if right then rightExit else leftExit, atom n, if right then outer else upd outer ⟨3⟩ (atom n))
  let step := CFG.Cyclic.step m ([] : List (Label × CFG.Block Reg Label signature.Instr))
  have atExit : CFG.Cyclic.run m entryLowered.source σ = iter step pending := by
    have read : σ ⟨0⟩ = value right n := by cases right <;> rfl
    cases right <;> simp [CFG.Cyclic.run, entryShape, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
      step, pending, outer, m, treeModel, value, read, upd]
  have finish : iter step pending = pure pending := by
    rw [congrFun (iterate_fixpoint step) pending]
    change (pure (Sum.inl pending) >>= _) = _
    rw [pure_bind]
    rfl
  change (CFG.Cyclic.run m entryLowered.source σ >>= _) = _
  rw [atExit, finish, pure_bind]
  cases right <;> rfl

example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) (Program.ofCFGEntry entryTyped).code =
      region model.raw (extend ambient (packedInput right n)) entryAdmission.program.code :=
  entryLowered.packed_roundTrip model entryTyped entryAdmission (input right n) ambient

-- The entry-only admission agrees with the original internal-block fixture
-- for both ordered exits at every supplied sum.
example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) entryAdmission.program.code =
      region model.raw (extend ambient (packedInput right n)) recompiled.program.code :=
  ((entryAdmission.packed_tree model (input right n) ambient).trans
    (entry_named_result right n)).trans
      (((recompiled.packed_tree model (input right n) ambient).trans (named_result right n)).symm)

section Equation

open Silmaril.Isotope.Institution.LetCase.WeakITree (algebra equationRoom)
open Silmaril.Elgot.ITree (ret_inj)

local notation "caseRoom" => (equationRoom signature)

private def entryPacketLocal : PacketLocal.Admission entryLowered :=
  PacketLocal.admit entryLowered Fin.elim0 (by decide)

private theorem entryPacketLocalRank : entryPacketLocal.acyclicCheck = true := by decide

-- The actual internal-block and entry-only expansions satisfy the same
-- equation, with a shared input and both ordered exits.
private theorem equation_accepts : (caseRoom).Sat (algebra (P := signature) model)
    (packetLocalCase.equation entryPacketLocal packetLocalCaseRank entryPacketLocalRank) := by
  apply (packetLocalCase.satisfies_iff_named model entryPacketLocal packetLocalCaseRank entryPacketLocalRank).2
  intro x
  rcases x with ⟨⟨⟩, left | right⟩
  · exact (named_result false left.down).trans (entry_named_result false left.down).symm
  · exact (named_result true right.down).trans (entry_named_result true right.down).symm

private def swapped : FiniteCFG signature.Instr 0 ports.exits.length ports.slots where
  entry := .case (.bv 0)
    (.br 1 (.pair (.bv 0) (.pair (.bv 0) .unit)))
    (.br 0 (.pair (.bv 0) (.pair (.bv 0) .unit)))
  block := Fin.elim0

private def swappedLowered : Lowered ports fields swapped :=
  (lowerFresh Fin.elim0 ports.context ports.exits ports.external fields swapped).get (by decide)

private def swappedPacketLocal : PacketLocal.Admission swappedLowered :=
  PacketLocal.admit swappedLowered Fin.elim0 (by decide)

private theorem swappedRank : swappedPacketLocal.acyclicCheck = true := by decide

-- Swapping the exit positions keeps both payloads and projected fields but
-- refutes the equation on the original caller's left input.
private theorem swapped_named_result :
    LiveOut.observe (P := signature) model ports fields swappedLowered.source (input false 5) =
      pure (output true 5) := by
  let m := treeModel model.raw
  let σ := store ports.names ports.context (input false 5)
  let pending : CFG.Cyclic.Transfer Reg Label (Value Runtime) := (rightExit, atom 5, upd σ ⟨2⟩ (atom 5))
  let step := CFG.Cyclic.step m ([] : List (Label × CFG.Block Reg Label signature.Instr))
  have shape : swappedLowered.source =
      ⟨.term (.case (.val (.var ⟨0⟩)) ⟨2⟩ (.br rightExit (.var ⟨2⟩))
        ⟨2⟩ (.br leftExit (.var ⟨2⟩))), []⟩ := rfl
  have read : σ ⟨0⟩ = .inl (atom 5) := rfl
  have atExit : CFG.Cyclic.run m swappedLowered.source σ = iter step pending := by
    simp [CFG.Cyclic.run, shape, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
      step, pending, m, treeModel, read, upd]
  have finish : iter step pending = pure pending := by
    rw [congrFun (iterate_fixpoint step) pending]
    change (pure (Sum.inl pending) >>= _) = _
    rw [pure_bind]
    rfl
  change (CFG.Cyclic.run m swappedLowered.source σ >>= _) = _
  rw [atExit, finish, pure_bind]
  rfl

private theorem equation_refutes : ¬ (caseRoom).Sat (algebra (P := signature) model)
    (packetLocalCase.equation swappedPacketLocal packetLocalCaseRank swappedRank) := by
  intro sat
  have same := (packetLocalCase.satisfies_iff_named model swappedPacketLocal
    packetLocalCaseRank swappedRank).1 sat (input false 5)
  rw [named_result false 5, swapped_named_result] at same
  cases congrArg Prod.snd (ret_inj.mp same)

example : packetLocalCase.program.denote model = entryPacketLocal.program.denote model :=
  (packetLocalCase.satisfies_iff_packed model entryPacketLocal
    packetLocalCaseRank entryPacketLocalRank).1 equation_accepts

example : packetLocalCase.program.denote model ≠ swappedPacketLocal.program.denote model :=
  fun same => equation_refutes ((packetLocalCase.satisfies_iff_packed model swappedPacketLocal
    packetLocalCaseRank swappedRank).2 same)

-- The second row loops to itself. Only the right arm of the reached first
-- row differs, making the same cycle reachable in one of the two tables.
private def loopFlat (reachable : Bool) : FiniteCFG signature.Instr 2 ports.exits.length ports.slots where
  entry := .br 0 (.bv 0)
  block := Fin.cases
    (.case (.bv 0)
      (.br 2 (.pair (.bv 0) (.pair (.bv 0) .unit)))
      (if reachable then .br 1 (.bv 0) else .br 3 (.pair (.bv 0) (.pair (.bv 0) .unit))))
    (fun _ => .br 1 (.bv 0))

private def loopLowered (reachable : Bool) : Lowered ports fields (loopFlat reachable) :=
  (lowerFresh (fun i => ⟨7 + i.val⟩) ports.context ports.exits ports.external fields (loopFlat reachable)).get
    (by cases reachable <;> decide)

private def loopAdmission (reachable : Bool) : PacketLocal.Admission (loopLowered reachable) :=
  PacketLocal.admit (loopLowered reachable) (Fin.cases choice (fun _ => num)) (by cases reachable <;> decide)

example :
    List.ofFn (fun i => (FlatLetCase.localTargets (loopAdmission false).versioned.table.code i).map Fin.val) =
      [[], [1]] := by decide

example :
    Positional.Rank.check (FlatLetCase.localTargets (loopAdmission false).versioned.table.code) = false :=
  by decide

private theorem deadLoopRank : (loopAdmission false).acyclicCheck = true := by decide

example :
    List.ofFn (fun i => (FlatLetCase.localTargets (loopAdmission true).versioned.table.code i).map Fin.val) =
      [[1], [1]] := by decide

example : (loopAdmission true).acyclicCheck = false := by decide

private def deadRow : List (Label × CFG.Block Reg Label signature.Instr) :=
  [(⟨8⟩, ⟨⟨1⟩, .term (.br ⟨8⟩ (.var ⟨1⟩))⟩)]

private theorem deadLoop_result (right : Bool) (n : Nat) :
    LiveOut.observe (P := signature) model ports fields (loopLowered false).source (input right n) =
      pure (output right n) :=
  named_result_with_tail (loopLowered false).source deadRow rfl rfl rfl rfl right n

-- The actual packed dispatcher still contains both rows. Expanding only
-- the first preserves both caller-dependent exit tags and the selected live-out.
example (right : Bool) (n : Nat) (ambient : Env Runtime) :
    region model.raw (extend ambient (packedInput right n)) (loopAdmission false).program.code =
      pure (output right n) :=
  ((loopAdmission false).packed_tree model (input right n) ambient).trans (deadLoop_result right n)

private theorem deadLoop_satisfies : (caseRoom).Sat (algebra (P := signature) model)
    ((loopAdmission false).equation packetLocalCase deadLoopRank packetLocalCaseRank) := by
  apply ((loopAdmission false).satisfies_iff_named model packetLocalCase deadLoopRank packetLocalCaseRank).2
  intro x
  rcases x with ⟨⟨⟩, left | right⟩
  · exact (deadLoop_result false left.down).trans (named_result false left.down).symm
  · exact (deadLoop_result true right.down).trans (named_result true right.down).symm

example : (loopAdmission false).program.denote model = packetLocalCase.program.denote model :=
  ((loopAdmission false).satisfies_iff_packed model packetLocalCase deadLoopRank packetLocalCaseRank).1
    deadLoop_satisfies

end Equation

section TwoCaptures

private abbrev twoPorts : Interface SortName Reg Label :=
  numberedInterface (.snoc (.snoc .nil choice) num) [leftExit, rightExit] (fun _ => num)

private def twoLabels (i : Fin 2) : Label := ⟨7 + i.val⟩
private def twoFields (_ : Label) : List (Reg × Ty SortName) := [(⟨4⟩, num)]
private def argumentType : Ty SortName := .product choice num

private def twoFlat : FiniteCFG signature.Instr 2 twoPorts.exits.length twoPorts.slots where
  entry := .br 0 (.pair (.bv 1) (.bv 0))
  block := Fin.cases (.br 1 (.bv 0)) fun _ =>
    .let₂ (.bv 0) (.case (.bv 1)
      (.br 2 (.pair (.bv 0) (.pair (.bv 1) .unit)))
      (.br 3 (.pair (.bv 0) (.pair (.bv 1) .unit))))

private def twoLowered : Lowered twoPorts twoFields twoFlat :=
  (lowerFresh twoLabels twoPorts.context twoPorts.exits twoPorts.external twoFields twoFlat).get (by decide)

private theorem twoTyped : twoFlat.HasType twoPorts.context (fun _ => argumentType)
    (LiveOut.exitInterface twoPorts twoFields).external :=
  NamedFlat.check_sound twoFlat twoPorts.context (fun _ => argumentType) _ (by decide)

-- Both internal targets use encounter order, which differs from slot order.
private def twoSlots : List (Fin 2) := [1, 0]

example : ∀ i, twoLowered.savedRegisters i = [⟨1⟩, ⟨0⟩] := by decide
example : ∀ i, twoLowered.packetProfile (fun _ => argumentType) (by decide) i =
    .product argumentType (.product choice (.product num .unit)) := by decide

private def twoRecompiled : LiveOut.Admission signature twoPorts twoFields twoLowered.source :=
  Straight.admitWithCaptures twoLowered (fun _ => argumentType) twoSlots
    (by decide) (by decide) (by decide)

private def twoInput (right : Bool) (n saved : Nat) :
    Ty.denote (AtomValues.carrier (κ := SortName)) (Region.packedInputType twoPorts.context.toList) :=
  (input right n, ⟨saved⟩)

private def twoArg (right : Bool) (n saved : Nat) : Value Runtime := .pair (value right n) (atom saved)

private def twoTransfer (i : Fin 2) (right : Bool) (n saved : Nat) :
    CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
  let σ := store twoPorts.names twoPorts.context (twoInput right n saved)
  let arg := twoArg right n saved
  (twoLabels i, arg, if i = 0 then σ else upd σ ⟨2⟩ arg)

private theorem twoStep (right : Bool) (n saved : Nat) :
    CFG.Cyclic.step (treeModel model.raw) twoLowered.source.blocks (twoTransfer 0 right n saved) =
      pure (.inr (twoTransfer 1 right n saved)) := by
  cases right <;> rfl

-- The store after the first block agrees at each supplied field. The two
-- fields retain distinct tags and travel in the actual destination order.
example (i : Fin 2) (right : Bool) (n saved : Nat) :
    CFG.Cyclic.Versioning.encode (treeModel model.raw)
        (withLiveOut (P := signature) twoFields twoLowered.source) (twoTransfer i right n saved) =
      (twoLabels i, .pair (twoArg right n saved) (.pair (value right n) (.pair (atom saved) .unit))) := by
  have route : ∀ j : Fin 2, CFG.Cyclic.Versioning.destinations
      (withLiveOut (P := signature) twoFields twoLowered.source) (twoLabels j) = some [⟨1⟩, ⟨0⟩] :=
    by decide
  have agrees (j : Fin 2) (_ : j ∈ twoSlots) :
      (twoTransfer i right n saved).2.2 ⟨j.val⟩ =
        inputEnv twoPorts.context (twoInput right n saved) j.val := by
    have initial := store_at twoPorts.names twoPorts.distinct twoPorts.context (twoInput right n saved) j
    have different : (⟨j.val⟩ : Reg) ≠ ⟨2⟩ :=
      fun eq => (Nat.ne_of_lt j.isLt) (congrArg ULift.down eq)
    by_cases first : i = 0 <;> simpa [twoTransfer, first, upd, different] using initial
  have packet := Straight.encode_captures twoLowered model twoSlots (twoInput right n saved)
    (twoTransfer i right n saved) (route i) agrees
  cases right <;> exact packet

private def twoOutput (right : Bool) (n saved : Nat) : Transfer Runtime :=
  let packet := (atom n).pair ((atom saved).pair .unit)
  (0, if right then .inr (.inl packet) else .inl packet)

set_option maxRecDepth 2048 in
private theorem twoNamedResult (right : Bool) (n saved : Nat) :
    LiveOut.observe (P := signature) model twoPorts twoFields twoLowered.source (twoInput right n saved) =
      pure (twoOutput right n saved) := by
  let m := treeModel model.raw
  let step := CFG.Cyclic.step m twoLowered.source.blocks
  let next := twoTransfer 1 right n saved
  let σ := upd (upd (upd (upd next.2.2 ⟨2⟩ next.2.1) ⟨3⟩ (value right n)) ⟨4⟩ (atom saved)) ⟨5⟩ (atom n)
  let done : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
    (if right then rightExit else leftExit, atom n, σ)
  have enter : CFG.Cyclic.run m twoLowered.source (store twoPorts.names twoPorts.context (twoInput right n saved)) =
      iter step (twoTransfer 0 right n saved) := by cases right <;> rfl
  let secondBlock : CFG.Block Reg Label signature.Instr :=
    ⟨⟨2⟩, .let2 ⟨3⟩ ⟨4⟩ (.val (.var ⟨2⟩))
      (.term (.case (.val (.var ⟨3⟩)) ⟨5⟩ (.br leftExit (.var ⟨5⟩))
        ⟨5⟩ (.br rightExit (.var ⟨5⟩))))⟩
  have firstStep : step (twoTransfer 0 right n saved) = pure (.inr next) := twoStep right n saved
  have selectArm : step next = pure (.inr done) := by
    change secondBlock.body.exec m
      (fun label arg store => pure (Sum.inr (α := CFG.Cyclic.Transfer Reg Label (Value Runtime)) (label, arg, store)))
      (upd next.2.2 secondBlock.param next.2.1) = _
    cases right <;>
      simp [secondBlock, next, twoTransfer, twoArg, done, σ, CFG.Body.exec, CFG.Term.exec,
        Op.eval, Val.eval, m, treeModel, value, upd, pure_bind]
  have exit : step done = pure (.inl done) := by cases right <;> rfl
  change (CFG.Cyclic.run m twoLowered.source (store twoPorts.names twoPorts.context (twoInput right n saved)) >>= _) = _
  rw [enter, congrFun (iterate_fixpoint step) (twoTransfer 0 right n saved), firstStep, pure_bind]
  change (iter step next >>= _) = _
  rw [congrFun (iterate_fixpoint step) next, selectArm, pure_bind]
  change (iter step done >>= _) = _
  rw [congrFun (iterate_fixpoint step) done, exit, pure_bind]
  change (pure done >>= _) = _
  rw [pure_bind]
  cases right <;> rfl

example (right : Bool) (n saved : Nat) (ambient : Env Runtime) :
    let packed := encodeValue (AtomValues.carrier (κ := SortName))
      (Region.packedInputType twoPorts.context.toList) (twoInput right n saved)
    region model.raw (extend ambient packed) (Program.ofCFGEntry twoTyped).code =
      region model.raw (extend ambient packed) twoRecompiled.program.code :=
  twoLowered.packed_roundTrip model twoTyped twoRecompiled (twoInput right n saved) ambient

example (right : Bool) (n saved : Nat) (ambient : Env Runtime) :
    let packed := encodeValue (AtomValues.carrier (κ := SortName))
      (Region.packedInputType twoPorts.context.toList) (twoInput right n saved)
    region model.raw (extend ambient packed) twoRecompiled.program.code = pure (twoOutput right n saved) :=
  (twoRecompiled.packed_tree model (twoInput right n saved) ambient).trans (twoNamedResult right n saved)

end TwoCaptures

section ProjectedCaptures

private abbrev projectedPorts : Interface SortName Reg Label :=
  numberedInterface twoPorts.context [leftExit] (fun _ => .unit)

private def noFields (_ : Label) : List (Reg × Ty SortName) := []

-- The first block's argument register is unused and outside the support.
-- The second uses the atom's entry register for its unit argument, so its
-- saved record contains only the still-carried sum.
private def projectedSource (back : Bool) : CFG Reg Label signature.Instr :=
  ⟨.let1 ⟨3⟩ (.val (.pair (.var ⟨1⟩) (.var ⟨0⟩))) (.term (.br (twoLabels 0) .unit)),
    [(twoLabels 0, ⟨⟨2⟩, .term (.br (twoLabels 1) .unit)⟩),
     (twoLabels 1, ⟨⟨0⟩, .term (.br (if back then twoLabels 0 else leftExit) (.var ⟨0⟩))⟩)]⟩

private abbrev projectedGraph (back : Bool) :=
  withLiveOut (P := signature) noFields (projectedSource back)

private def projectedRead (back : Bool) :
    Option (FiniteCFG signature.Instr 2 projectedPorts.exits.length projectedPorts.slots) :=
  NamedFlat.elaborateAt (projectedGraph back) projectedPorts.exits projectedPorts.names 2 rfl

private def projectedCode (back : Bool) : FiniteCFG signature.Instr 2 projectedPorts.exits.length projectedPorts.slots :=
  (projectedRead back).get (by cases back <;> decide)

private def projectedLowered (back : Bool) : Lowered projectedPorts noFields (projectedCode back) where
  source := projectedSource back
  closed := by
    have each : ∀ i : Fin (projectedGraph back).blocks.length,
        (projectedGraph back).blocks[i].2.body.toRegion.fv ⊆ {(projectedGraph back).blocks[i].2.param} := by
      cases back <;> decide
    intro item member
    obtain ⟨i, valid, eq⟩ := List.getElem_of_mem member
    rw [← eq]
    exact each ⟨i, valid⟩
  count := rfl
  readback := (Option.some_get _).symm

private def projectedLayouts (i : Fin 2) : List (Fin 2) :=
  if i = 0 then [1, 0] else [1]

private def projectedAdmission : LiveOut.Admission signature projectedPorts noFields (projectedSource false) :=
  (CaptureDemand.admitReference (projectedLowered false) (fun _ => .unit)).get (by decide)

example : CaptureDemand.referenceEntry (projectedLowered false) = [1, 0] ∧
    List.ofFn (CaptureDemand.referenceLayouts (projectedLowered false)) = [[1, 0], [1]] := by decide

example : List.ofFn (CaptureDemand.ordered (projectedGraph false)
    (fun j : Fin 2 => (⟨j.val⟩ : Reg)) twoSlots) = [[], []] := by decide

example : (CaptureDemand.admitReference (projectedLowered true) (fun _ => .unit)).isNone = true := by decide

example : CFG.Cyclic.Versioning.registers (projectedGraph false) = [⟨1⟩, ⟨0⟩] := by decide
example : ∀ i, (projectedLowered false).packetProfile (fun _ => .unit) (by decide) i =
    if i.val = 0 then .product .unit (.product choice (.product num .unit))
    else .product .unit (.product choice .unit) := by decide

private def projectedTransfer (i : Fin 2) (right : Bool) (n saved : Nat) :
    CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
  let σ := store projectedPorts.names projectedPorts.context (twoInput right n saved)
  let assigned := upd σ ⟨3⟩ (twoArg right n saved)
  (twoLabels i, .unit, if i = 0 then assigned else upd assigned ⟨2⟩ .unit)

private def projectedPacket (right : Bool) (n : Nat) : Label × Value Runtime :=
  (twoLabels 1, .pair .unit (.pair (value right n) .unit))

private theorem encodeProjected (right : Bool) (n saved : Nat) :
    CFG.Cyclic.Versioning.encode (treeModel model.raw) (projectedGraph false) (projectedTransfer 1 right n saved) =
      projectedPacket right n := by
  have route : CFG.Cyclic.Versioning.destinations (projectedGraph false) (twoLabels 1) = some [⟨1⟩] := by decide
  have same : (projectedTransfer 1 right n saved).2.2 ⟨1⟩ =
      inputEnv projectedPorts.context (twoInput right n saved) 1 := by cases right <;> rfl
  have packet := Straight.encode_capture (projectedLowered false) model 1 (twoInput right n saved)
    (projectedTransfer 1 right n saved) route same
  cases right <;> exact packet

-- The compiled step decodes the full packet and emits the smaller one.
example (right : Bool) (n saved : Nat) :
    let m := treeModel model.raw
    let input := store projectedPorts.version.names projectedPorts.context (twoInput right n saved)
    CFG.Cyclic.stepSSA m (CFG.Cyclic.Versioning.compile (projectedGraph false)).blocks input
      (CFG.Cyclic.Versioning.encode m (projectedGraph false) (projectedTransfer 0 right n saved)) =
      pure (.inr (projectedPacket right n)) := by
  let m := treeModel model.raw
  let graph := projectedGraph false
  let input := store projectedPorts.version.names projectedPorts.context (twoInput right n saved)
  have actual : CFG.Cyclic.step m graph.blocks (projectedTransfer 0 right n saved) =
      pure (.inr (projectedTransfer 1 right n saved)) := by cases right <;> rfl
  have encoded : CFG.Cyclic.Versioning.encode m graph (projectedTransfer 1 right n saved) =
      projectedPacket right n := encodeProjected right n saved
  change CFG.Cyclic.stepSSA m (CFG.Cyclic.Versioning.compile graph).blocks input
      (CFG.Cyclic.Versioning.encode m graph (projectedTransfer 0 right n saved)) = _
  rw [← CFG.Cyclic.Versioning.step_commutes m ⟨fun _ _ => rfl⟩ graph input, actual, map_pure, Sum.map_inr, encoded]

-- The second block accepts the smaller packet and reaches the declared exit.
example (right : Bool) (n saved : Nat) :
    let m := treeModel model.raw
    let input := store projectedPorts.version.names projectedPorts.context (twoInput right n saved)
    CFG.Cyclic.stepSSA m (CFG.Cyclic.Versioning.compile (projectedGraph false)).blocks input
      (projectedPacket right n) = pure (.inr (leftExit, .pair .unit .unit)) := by
  let m := treeModel model.raw
  let graph := projectedGraph false
  let input := store projectedPorts.version.names projectedPorts.context (twoInput right n saved)
  let pending := projectedTransfer 1 right n saved
  have encoded : CFG.Cyclic.Versioning.encode m graph pending = projectedPacket right n :=
    encodeProjected right n saved
  have actual : CFG.Cyclic.step m graph.blocks pending =
      pure (.inr (leftExit, .pair .unit .unit, upd pending.2.2 ⟨0⟩ .unit)) := by cases right <;> rfl
  change CFG.Cyclic.stepSSA m (CFG.Cyclic.Versioning.compile graph).blocks input (projectedPacket right n) = _
  rw [← encoded, ← CFG.Cyclic.Versioning.step_commutes m ⟨fun _ _ => rfl⟩ graph input, actual, map_pure, Sum.map_inr]
  rfl

private theorem projectedTyped : (projectedCode false).HasType projectedPorts.context (fun _ => .unit)
    (LiveOut.exitInterface projectedPorts noFields).external :=
  NamedFlat.check_sound (projectedCode false) projectedPorts.context (fun _ => .unit) _ (by decide)

example (right : Bool) (n saved : Nat) (ambient : Env Runtime) :
    let packed := encodeValue (AtomValues.carrier (κ := SortName))
      (Region.packedInputType projectedPorts.context.toList) (twoInput right n saved)
    region model.raw (extend ambient packed) (Program.ofCFGEntry projectedTyped).code =
      region model.raw (extend ambient packed) projectedAdmission.program.code :=
  (projectedLowered false).packed_roundTrip model projectedTyped projectedAdmission (twoInput right n saved) ambient

-- A new back edge would require the atom again. The second block now has
-- its unit argument in that register, at the wrong type for the saved slot.
example : Straight.checks (projectedLowered true) (fun _ => .unit) = true ∧
    Straight.checksCaptureEdges (projectedLowered true) projectedLayouts = false ∧
    (NamedFlat.compile (projectedGraph true) projectedPorts.exits projectedPorts.names).isSome = true ∧
    ((projectedLowered true).reAdmit (fun _ => .unit)).isNone = true := by decide

example :
    let table := (NamedFlat.compile (projectedGraph true) projectedPorts.exits projectedPorts.names).get (by decide)
    let packets := (projectedLowered true).packetProfile (fun _ => .unit) (by decide)
    let types := SSA.FiniteSum.append packets (LiveOut.exitInterface projectedPorts noFields).external
    checkBody types projectedPorts.context table.entry = true ∧
      checkBody types (.snoc projectedPorts.context (packets (0 : Fin 2))) (table.block (0 : Fin 2)) = true ∧
      checkBody types (.snoc projectedPorts.context (packets (1 : Fin 2))) (table.block (1 : Fin 2)) = false := by
  decide

-- The opt-in compiler also admits the certified back-edge variant.
-- Its slots are empty at both destinations, so the atom overwritten by
-- the block parameter is never requested as an unchanged capture.
private def packetLocalAdmission (back : Bool) : PacketLocal.Admission (projectedLowered back) :=
  PacketLocal.admit (projectedLowered back) (fun _ => .unit) (by cases back <;> decide)

example : ∀ i : Fin 2, Straight.packetLocalProfile (projectedLowered false) (fun _ => .unit) i =
    .product .unit .unit := fun _ => rfl

-- Both encodings come from the compiler entry routes. The default
-- nonempty records are checked above, whereas the opt-in records are unit.
example (i : Fin 2) (right : Bool) (n saved : Nat) :
    CFG.Cyclic.Versioning.encodePacketLocal (treeModel model.raw) (projectedGraph false)
      (projectedTransfer i right n saved) = (twoLabels i, .pair .unit .unit) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl

example (right : Bool) (n saved : Nat) :
    let m := treeModel model.raw
    let input := store projectedPorts.version.names projectedPorts.context (twoInput right n saved)
    CFG.Cyclic.stepSSA m (CFG.Cyclic.Versioning.compilePacketLocal (projectedGraph false)).blocks input
      (twoLabels 0, .pair .unit .unit) = pure (.inr (twoLabels 1, .pair .unit .unit)) := by
  let m := treeModel model.raw
  let graph := projectedGraph false
  let input := store projectedPorts.version.names projectedPorts.context (twoInput right n saved)
  have actual : CFG.Cyclic.step m graph.blocks (projectedTransfer 0 right n saved) =
      pure (.inr (projectedTransfer 1 right n saved)) := by cases right <;> rfl
  have commute := CFG.Cyclic.Versioning.stepPacketLocal_commutes m ⟨fun _ _ => rfl⟩ graph
    (projectedLowered false).closed input (projectedTransfer 0 right n saved)
  rw [actual, map_pure, Sum.map_inr] at commute
  exact commute.symm

-- Continue across the previous back edge with another empty record.
example (right : Bool) (n saved : Nat) :
    let m := treeModel model.raw
    let input := store projectedPorts.version.names projectedPorts.context (twoInput right n saved)
    CFG.Cyclic.stepSSA m (CFG.Cyclic.Versioning.compilePacketLocal (projectedGraph true)).blocks input
      (twoLabels 1, .pair .unit .unit) = pure (.inr (twoLabels 0, .pair .unit .unit)) := by
  let m := treeModel model.raw
  let graph := projectedGraph true
  let input := store projectedPorts.version.names projectedPorts.context (twoInput right n saved)
  let pending := projectedTransfer 1 right n saved
  let back : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
    (twoLabels 0, .unit, upd pending.2.2 ⟨0⟩ .unit)
  have actual : CFG.Cyclic.step m graph.blocks pending = pure (.inr back) := rfl
  have commute := CFG.Cyclic.Versioning.stepPacketLocal_commutes m ⟨fun _ _ => rfl⟩ graph
    (projectedLowered true).closed input pending
  rw [actual, map_pure, Sum.map_inr] at commute
  exact commute.symm

example (right : Bool) (n saved : Nat) (ambient : Env Runtime) :
    let packed := encodeValue (AtomValues.carrier (κ := SortName))
      (Region.packedInputType projectedPorts.context.toList) (twoInput right n saved)
    region model.raw (extend ambient packed) (Program.ofCFGEntry projectedTyped).code =
      region model.raw (extend ambient packed) (packetLocalAdmission false).program.code :=
  (packetLocalAdmission false).packed_roundTrip model projectedTyped (twoInput right n saved) ambient

example (right : Bool) (n saved : Nat) (ambient : Env Runtime) :
    let packed := encodeValue (AtomValues.carrier (κ := SortName))
      (Region.packedInputType projectedPorts.context.toList) (twoInput right n saved)
    region model.raw (extend ambient packed) (packetLocalAdmission false).program.code =
      region model.raw (extend ambient packed) projectedAdmission.program.code :=
  ((packetLocalAdmission false).packed_tree model (twoInput right n saved) ambient).trans
    (projectedAdmission.packed_tree model (twoInput right n saved) ambient).symm

example (right : Bool) (n saved : Nat) (ambient : Env Runtime) :
    let packed := encodeValue (AtomValues.carrier (κ := SortName))
      (Region.packedInputType projectedPorts.context.toList) (twoInput right n saved)
    region model.raw (extend ambient packed) (packetLocalAdmission true).program.code =
      LiveOut.observe model projectedPorts noFields (projectedSource true) (twoInput right n saved) :=
  (packetLocalAdmission true).packed_tree model (twoInput right n saved) ambient

example : (packetLocalAdmission true).acyclicCheck = false := by decide

end ProjectedCaptures

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Case
