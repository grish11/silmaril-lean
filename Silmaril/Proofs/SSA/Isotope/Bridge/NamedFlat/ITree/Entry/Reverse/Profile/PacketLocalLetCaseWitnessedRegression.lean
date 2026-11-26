module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Witnessed.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Admission.Thms

/-! # A written LetCase request and two ordered live-out exits -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed.Tests

open LambdaSSA (Region)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Acyclic.Positional.Capture
open LambdaSSA.Acyclic.Positional.Capture.Reverse (ResultGrammar)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (vis diverge vis_bind)
open Isotope.Semantics (encodeValue)
open Isotope.Institution.LetCase.WeakITree (algebra equationRoom)

private abbrev SortName := ULift.{1} Unit
private abbrev Label := ULift.{1} Nat
private abbrev Atom := ULift.{1} Nat

private def num : Ty SortName := .base ⟨()⟩
private def choice : Ty SortName := .coprod num num

private inductive Op : Type 1
  | pick
  deriving DecidableEq

private inductive Event : Type → Type
  | choose : Event Bool

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private instance : HasTy Op (Ty SortName) := ⟨fun _ => num, fun _ => choice⟩
private instance : HasEff Op Bool := ⟨fun _ => true⟩

private def sig : FlatInstitution.Signature.{0, 1} SortName where
  Instr := Op

private instance : DecidableEq sig.Instr := inferInstanceAs (DecidableEq Op)

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))
private abbrev C := AtomValues.carrier (κ := SortName)

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event sig.Instr where
  instructions :=
    { denote := fun _ x => vis Event.choose (fun right => pure (if right then .inr x else .inl x))
      denotePure := fun _ h => nomatch h
      denote_pure := fun _ h => nomatch h }
  raw := fun _ x =>
    match x with
    | .atom n => vis Event.choose (fun right => pure (if right then .inr (.atom n) else .inl (.atom n)))
    | _ => diverge
  compatible := by
    dsimp only
    intro f x
    change (vis Event.choose (fun right => pure (if right then .inr (.atom ⟨⟨()⟩, x⟩)
      else .inl (.atom ⟨⟨()⟩, x⟩)))) =
      (vis Event.choose (fun right => pure (if right then Sum.inr x else Sum.inl x)) >>=
        fun y => pure (encodeValue C choice y))
    rw [vis_bind]
    congr 1
    funext reply
    cases reply <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind] <;> rfl

private abbrev context : BoundCtx (Ty SortName) 1 := .snoc .nil num
private abbrev exits : List Label := [⟨22⟩, ⟨11⟩]
private def external (_ : Fin exits.length) : Ty SortName := .unit
private def fields (_ : Label) : List (Register × Ty SortName) := [(⟨1⟩, num)]
private abbrev ports := numberedInterface context exits external
private abbrev D := (LiveOut.exitInterface ports fields).external
private abbrev B := Region.packedExitType (List.ofFn D)
private abbrev A := Region.packedInputType context.toList

-- Written directly in native LetCase syntax. The two tagged packets have
-- the same unit payload but carry the caller's value as a selected live-out.
private def written : Operand sig.Instr context B :=
  ⟨.let₁ (.bv 0) (.case (.op .pick (.bv 0))
      (.let₁ (.pair .unit (.pair (.bv 0) .unit)) (.inl (.bv 0)))
      (.let₁ (.pair .unit (.pair (.bv 0) .unit)) (.inr (.inl (.bv 0))))),
    .let₁ .bv (.case (.op .bv)
      (.let₁ (.pair .unit (.pair .bv .unit)) (.inl .bv))
      (.let₁ (.pair .unit (.pair .bv .unit)) (.inr (.inl .bv))))⟩

private def grammar : ResultGrammar (L := List.ofFn D) written :=
  ⟨⟨num, ⟨.bv 0, .bv⟩, .case ⟨.op .pick (.bv 0), .op .bv⟩
      (.local (.jump ⟨.pair .unit (.pair (.bv 0) .unit), .pair .unit (.pair .bv .unit)⟩ (.exit (i := 0) rfl)))
      (.local (.jump ⟨.pair .unit (.pair (.bv 0) .unit), .pair .unit (.pair .bv .unit)⟩ (.exit (i := 1) rfl)))⟩,
    rfl⟩

private def labels (i : Fin (grammar.toTable.size + 1)) : Label := ⟨7 + i.val⟩

private theorem compiled_ok : (compile? (fields := fields) grammar labels).isSome = true := by decide +kernel

private def compiled : Compiled (fields := fields) grammar :=
  (compile? (fields := fields) grammar labels).get compiled_ok

example : grammar.toTable.size + 1 = 3 := rfl

example : (equationRoom sig).Sat (algebra (P := sig) model) compiled.equation :=
  compiled.satisfies model

example : (Program.ofCFGEntry grammar.toTable.toFlat_hasType).denote model =
    compiled.admission.program.denote model :=
  compiled.packed_eq model

private def packet (x : Atom) : Value Runtime := .pair .unit (.pair (.atom ⟨⟨()⟩, x⟩) .unit)

private theorem source_result (x : Atom) :
    (sourceTree (fields := fields) model written (PUnit.unit, x) >>= fun b => pure (0, encodeValue C B b)) =
      vis Event.choose (fun right => pure (0, if right then .inr (.inl (packet x)) else .inl (packet x))) := by
  simp only [sourceTree, written, LetCase.LocallyNameless.Derivation.denote, pure_bind]
  let request (a : Atom) : ModelTree Event (Atom ⊕ Atom) :=
    vis Event.choose (fun right => pure (if right then Sum.inr a else Sum.inl a))
  change ((((pure x : ModelTree Event Atom) >>= request) >>= _) >>= _) = _
  rw [pure_bind]
  change ((vis Event.choose _ >>= _) >>= _) = _
  erw [vis_bind, vis_bind]
  congr 1
  funext right
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> erw [pure_bind] <;>
    dsimp [Semantics.CoproductModel.coprodEquiv, Semantics.ProductModel.productEquiv,
      Semantics.UnitModel.unitEquiv, Semantics.BoundEnv.snoc, Record.field, Equiv.refl, Equiv.symm, DFunLike.coe, EquivLike.coe, Equiv.instEquivLike, id] <;>
    repeat' (first | rfl | erw [pure_bind])

example (x : Atom) :
    LiveOut.observe model ports fields compiled.lowered.source (PUnit.unit, x) =
      vis Event.choose (fun right => pure (0, if right then .inr (.inl (packet x)) else .inl (packet x))) :=
  (compiled.named_tree model (PUnit.unit, x)).symm.trans (source_result x)

example (x : Atom) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue C A (PUnit.unit, x))) compiled.admission.program.code =
      vis Event.choose (fun right => pure (0, if right then .inr (.inl (packet x)) else .inl (packet x))) :=
  (compiled.packed_tree model (PUnit.unit, x) ambient).trans (source_result x)

-- The captured reverse compiler permits this older input read, but the
-- unchanged packet-local input leaves no corresponding block-local name.
private def readsAmbient : Reverse.Program sig.Instr context (List.ofFn D) :=
  ⟨num, ⟨.bv 0, .bv⟩,
    .jump ⟨.pair .unit (.pair (.bv 1) .unit), .pair .unit (.pair .bv .unit)⟩ (.exit (i := 0) rfl)⟩

private def ambientGrammar : ResultGrammar readsAmbient.toLetCase := ⟨readsAmbient, rfl⟩

private def ambientLabels (i : Fin (ambientGrammar.toTable.size + 1)) : Label := ⟨7 + i.val⟩

example : (lower (freshRegisters 1) ports.names ambientLabels (fun i => exits[i])
    (ambientGrammar.toTable.toFlat List.length_ofFn)).isSome = true := by decide

example : (lowerFresh ambientLabels context exits external fields
    (ambientGrammar.toTable.toFlat List.length_ofFn)).isNone = true := by decide

example : (compile? (fields := fields) ambientGrammar ambientLabels).isNone = true := by decide

-- After attachment, the old emission reads the incoming packet at slot
-- zero. The original typed row reads the older caller field at slot one.
private def oldSource :=
  (lower (freshRegisters 1) ports.names ambientLabels (fun i => exits[i])
    (ambientGrammar.toTable.toFlat List.length_ofFn)).get (by decide)

example : (flat (fields := fields) ambientGrammar none).block 0 =
    .br 1 (.pair .unit (.pair (.bv 1) .unit)) := by decide

example : ((elaborate (withLiveOut (P := sig) fields oldSource) exits ports.names).map
    (fun code => code.block ⟨0, by decide⟩)) = some (.br 1 (.pair .unit (.pair (.bv 0) .unit))) := by decide

-- Decode the old packet into register 2, then replace packet register 1
-- with the carried caller field. The outward projection stays register 1.
private def carryRegisters : Registers Register :=
  ⟨⟨1⟩, fun depth => if depth = 1 then ⟨1⟩ else ⟨2 + depth⟩⟩

private def ambientCompiled : Compiled (fields := fields) ambientGrammar (some 0) :=
  (compileCarry? (fields := fields) ambientGrammar 0 carryRegisters ambientLabels).get (by decide)

example : (equationRoom sig).Sat (algebra (P := sig) model) ambientCompiled.equation :=
  ambientCompiled.satisfies model

example : (Program.ofCFGEntry ambientGrammar.toTable.toFlat_hasType).denote model =
    ambientCompiled.admission.program.denote model :=
  ambientCompiled.packed_eq model

-- A unit incoming argument makes the carried number distinguishable from
-- the original packet. The same input, exit order and live-out register
-- are used by the named run, the packed reversion and the equation.
private def readsAmbientWithUnit : Reverse.Program sig.Instr context (List.ofFn D) :=
  ⟨.unit, ⟨.unit, .unit⟩,
    .jump ⟨.pair .unit (.pair (.bv 1) .unit), .pair .unit (.pair .bv .unit)⟩ (.exit (i := 0) rfl)⟩

private def unitWritten : Operand sig.Instr context B :=
  ⟨.let₁ .unit (.let₁ (.pair .unit (.pair (.bv 1) .unit)) (.inl (.bv 0))),
    .let₁ .unit (.let₁ (.pair .unit (.pair .bv .unit)) (.inl .bv))⟩

private def unitGrammar : ResultGrammar (L := List.ofFn D) unitWritten := ⟨readsAmbientWithUnit, rfl⟩
private def unitLabels (i : Fin (unitGrammar.toTable.size + 1)) : Label := ⟨7 + i.val⟩

private def unitCompiled : Compiled (fields := fields) unitGrammar (some 0) :=
  (compileCarry? (fields := fields) unitGrammar 0 carryRegisters unitLabels).get (by decide)

example : (flat (fields := fields) unitGrammar (some 0)).entry = .br 0 (.pair .unit (.bv 0)) ∧
    (flat (fields := fields) unitGrammar (some 0)).block 0 =
      .let₂ (.bv 0) (.br 1 (.pair .unit (.pair (.bv 0) .unit))) := by decide

private theorem unit_result (x : Atom) :
    (sourceTree (fields := fields) model unitWritten (PUnit.unit, x) >>=
      fun b => pure (0, encodeValue C B b)) = pure (0, .inl (packet x)) := by
  simp only [sourceTree, unitWritten, LetCase.LocallyNameless.Derivation.denote, pure_bind]
  repeat' (first | rfl | erw [pure_bind])

example (x : Atom) :
    LiveOut.observe model ports fields unitCompiled.lowered.source (PUnit.unit, x) =
      pure (0, .inl (packet x)) :=
  (unitCompiled.named_tree model (PUnit.unit, x)).symm.trans (unit_result x)

example (x : Atom) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue C A (PUnit.unit, x))) unitCompiled.admission.program.code =
      pure (0, .inl (packet x)) :=
  (unitCompiled.packed_tree model (PUnit.unit, x) ambient).trans (unit_result x)

example : (equationRoom sig).Sat (algebra (P := sig) model) unitCompiled.equation :=
  unitCompiled.satisfies model

-- Carry two differently typed older inputs through a unit row and then
-- a number row. The selected registers and second outward position are fixed.
private abbrev mixedContext : BoundCtx (Ty SortName) 2 := .snoc context choice
private def mixedFields (_ : Label) : List (Register × Ty SortName) := [(⟨6⟩, num), (⟨4⟩, choice)]
private abbrev mixedPorts := numberedInterface mixedContext exits external
private abbrev mixedExits := (LiveOut.exitInterface mixedPorts mixedFields).external
private abbrev MixedOutput := Region.packedExitType (List.ofFn mixedExits)

private def mixedWritten : Operand sig.Instr mixedContext MixedOutput :=
  ⟨.let₁ .unit (.let₁ (.bv 2)
      (.let₁ (.pair .unit (.pair (.bv 3) (.pair (.bv 2) .unit))) (.inr (.inl (.bv 0))))),
    .let₁ .unit (.let₁ .bv (.let₁ (.pair .unit (.pair .bv (.pair .bv .unit))) (.inr (.inl .bv))))⟩

private def mixedGrammar : ResultGrammar (L := List.ofFn mixedExits) mixedWritten :=
  ⟨⟨.unit, ⟨.unit, .unit⟩,
    .jump (B := num) ⟨.bv 2, .bv⟩ (.local
      (.jump ⟨.pair .unit (.pair (.bv 2) (.pair (.bv 1) .unit)), .pair .unit (.pair .bv (.pair .bv .unit))⟩
        (.exit (i := 1) rfl)))⟩, rfl⟩

private def mixedLabels (i : Fin (mixedGrammar.toTable.size + 1)) : Label := ⟨7 + i.val⟩
private def mixedSlots : List (Fin 2) := [1, 0]
private def mixedRegisters : Registers Register := freshRegisters 2

example : inferredSlots (fields := fields) grammar = [] := by decide

example : inferredSlots (fields := mixedFields) mixedGrammar = mixedSlots := by decide

private theorem mixedCompiled_ok :
    (compileInferred? (fields := mixedFields) mixedGrammar mixedRegisters mixedLabels).isSome = true := by
  decide +kernel

private def mixedCompiled : CompiledList (fields := mixedFields) mixedGrammar (inferredSlots mixedGrammar) :=
  (compileInferred? (fields := mixedFields) mixedGrammar mixedRegisters mixedLabels).get mixedCompiled_ok

example : packetTypesList (fields := mixedFields) mixedGrammar mixedSlots 0 = .product (.product .unit num) choice ∧
    packetTypesList (fields := mixedFields) mixedGrammar mixedSlots 1 = .product (.product num num) choice := by decide

example : (flatList (fields := mixedFields) mixedGrammar mixedSlots).entry =
    .br 0 (.pair (.pair .unit (.bv 1)) (.bv 0)) := by decide

example : (flatList (fields := mixedFields) mixedGrammar mixedSlots).block 0 =
    .let₂ (.bv 0) (.let₂ (.bv 1) (.br 1 (.pair (.pair (.bv 0) (.bv 0)) (.bv 2)))) := by decide

example : (compileCarryList? (fields := mixedFields) mixedGrammar [1] mixedRegisters mixedLabels).isNone = true := by decide

example : (compileCarryList? (fields := mixedFields) mixedGrammar [0, 1] mixedRegisters mixedLabels).isNone = true := by decide

private def mixedPacket (x : Atom) (b : Atom ⊕ Atom) : Value Runtime :=
  .pair .unit (.pair (.atom ⟨⟨()⟩, x⟩) (.pair (encodeValue C choice b) .unit))

private theorem mixed_result (x : Atom) (b : Atom ⊕ Atom) :
    (sourceTree (fields := mixedFields) model mixedWritten ((PUnit.unit, x), b) >>=
      fun y => pure (0, encodeValue C MixedOutput y)) = pure (0, .inr (.inl (mixedPacket x b))) := by
  simp only [sourceTree, mixedWritten, LetCase.LocallyNameless.Derivation.denote, pure_bind]
  repeat' (first | rfl | erw [pure_bind])

example (x : Atom) (b : Atom ⊕ Atom) :
    LiveOut.observe model mixedPorts mixedFields mixedCompiled.lowered.source ((PUnit.unit, x), b) =
      pure (0, .inr (.inl (mixedPacket x b))) :=
  (mixedCompiled.named_tree model ((PUnit.unit, x), b)).symm.trans (mixed_result x b)

example (x : Atom) (b : Atom ⊕ Atom) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue C (Region.packedInputType mixedContext.toList)
      ((PUnit.unit, x), b))) mixedCompiled.admission.program.code =
        pure (0, .inr (.inl (mixedPacket x b))) :=
  (mixedCompiled.packed_tree model ((PUnit.unit, x), b) ambient).trans (mixed_result x b)

example : (Program.ofCFGEntry mixedGrammar.toTable.toFlat_hasType).denote model =
    mixedCompiled.admission.program.denote model :=
  mixedCompiled.packed_eq model

example : (equationRoom sig).Sat (algebra (P := sig) model) mixedCompiled.equation :=
  mixedCompiled.satisfies model

-- The oldest slot is used at entry only. The row reads the newer sum
-- underneath a product decoder and the middle number inside a case arm's
-- nested operand. Packet and local reads must not select caller slots.
private abbrev shiftedContext : BoundCtx (Ty SortName) 3 := .snoc (.snoc context num) choice

private def shiftedTable : LambdaSSA.FiniteCFG sig.Instr 1 1 3 :=
  ⟨.br 0 (.bv 2), fun _ =>
    .let₂ (.pair (.bv 0) .unit)
      (.case (.bv 3)
        (.br 1 (.let₁ (.bv 0) (.pair (.bv 0) (.bv 6))))
        (.br 1 (.pair (.bv 0) (.bv 2))))⟩

example : shiftedTable.HasType shiftedContext (fun _ => num) (fun _ => .product num num) :=
  ⟨.br .bv, fun _ => .let₂ (.pair .bv .unit)
    (.case .bv (.br (.let₁ .bv (.pair .bv .bv))) (.br (.pair .bv .bv)))⟩

open Capture.Carry (graphList inferSlots infer_packetOnly) in
example : inferSlots shiftedTable = [1, 0] ∧
    ((graphList shiftedTable (inferSlots shiftedTable)).block 0).erase.Scoped 2 1 :=
  ⟨by decide, infer_packetOnly shiftedTable 0⟩

-- A packet-only row can still fail the named grammar's operand check.
open Capture.Carry (graphList inferSlots) in
example : (lower (freshRegisters 3) (fun i => (⟨i.val⟩ : Register))
    (fun _ => (⟨7⟩ : Label)) (fun _ => ⟨22⟩)
    (graphList shiftedTable (inferSlots shiftedTable))).isNone = true := by decide

-- The original variable alias contracts in the case arm. Its old flat
-- pair was not a mutable exit packet: the second number was plain data.
open Capture.Carry (graphList inferSlots infer_packetOnly) in
example :
    (Materialize.graph shiftedTable).block 0 =
      .let₂ (.pair (.bv 0) .unit)
        (.case (.bv 3) (.br 1 (.pair (.bv 0) (.bv 5))) (.br 1 (.pair (.bv 0) (.bv 2)))) ∧
    (lower (freshRegisters 3) (fun i => (⟨i.val⟩ : Register))
      (fun _ => (⟨7⟩ : Label)) (fun _ => ⟨22⟩)
      (graphList (Materialize.graph shiftedTable) (inferSlots (Materialize.graph shiftedTable)))).isSome = true :=
  ⟨by decide, by decide⟩

private abbrev shiftedExits : List Label := [⟨22⟩]
private def shiftedOldType (_ : Fin shiftedExits.length) : Ty SortName := .product num num
private abbrev shiftedPorts := numberedInterface shiftedContext shiftedExits shiftedOldType

example (old : Fin shiftedExits.length → Ty SortName) (fields' : Label → List (Register × Ty SortName)) :
    (LiveOut.exitInterface (numberedInterface shiftedContext shiftedExits old) fields').external ⟨0, Nat.zero_lt_succ 0⟩ ≠
      .product num num := by
  change Ty.product (old 0) (LiveOut.recordType (fields' ⟨22⟩)) ≠ .product num num
  cases fields' ⟨22⟩ <;> simp [LiveOut.recordType, num]

-- Keep both original payload components and explicitly project the middle
-- caller number as a live-out. The entry's leading operand let performs a
-- real request, so materialization must bind it before the internal jump.
private def shiftedFields (_ : Label) : List (Register × Ty SortName) := [(⟨7⟩, num)]

private def shiftedLiveTable : LambdaSSA.FiniteCFG sig.Instr 1 shiftedExits.length 3 :=
  ⟨.br 0 (.let₁ (.op .pick (.bv 2)) (.bv 3)), fun _ =>
    .let₂ (.pair (.bv 0) .unit)
      (.case (.bv 3)
        (.br 1 (.let₁ (.bv 0) (.pair (.pair (.bv 0) (.bv 6)) (.pair (.bv 6) .unit))))
        (.br 1 (.pair (.pair (.bv 0) (.bv 2)) (.pair (.bv 5) .unit))))⟩

private theorem shiftedTyped :
    shiftedLiveTable.HasType shiftedContext (fun _ => num)
      (LiveOut.exitInterface shiftedPorts shiftedFields).external :=
  ⟨.br (.let₁ (.op .bv) .bv), fun _ => .let₂ (.pair .bv .unit)
    (.case .bv (.br (.let₁ .bv (.pair (.pair .bv .bv) (.pair .bv .unit))))
      (.br (.pair (.pair .bv .bv) (.pair .bv .unit))))⟩

private def shiftedRegisters : Registers Register := freshRegisters 3
private def shiftedLabels (_ : Fin 1) : Label := ⟨7⟩

private def shiftedCompile :=
  compileFlatInferred? (P := sig) (context := shiftedContext) (external := shiftedOldType) (fields := shiftedFields)
    (Materialize.graph shiftedLiveTable) (fun _ => num) shiftedRegisters shiftedLabels

private theorem shiftedCompile_ok : shiftedCompile.isSome = true := by decide +kernel
private def shiftedCompiled := shiftedCompile.get shiftedCompile_ok

example : Capture.Carry.inferSlots (Materialize.graph shiftedLiveTable) = [1, 0] := by decide

example : shiftedCompiled.lowered.source.entry =
    .let1 ⟨4⟩ (.app .pick (.var ⟨2⟩))
      (.term (.br ⟨7⟩ (.pair (.pair (.var ⟨2⟩) (.var ⟨1⟩)) (.var ⟨0⟩)))) := by decide +kernel

private def overwritesInput : Registers Register :=
  { shiftedRegisters with localAt := fun depth => if depth = 0 then ⟨2⟩ else shiftedRegisters.localAt depth }

example : (compileFlatInferred? (P := sig) (context := shiftedContext) (external := shiftedOldType)
    (fields := shiftedFields) (Materialize.graph shiftedLiveTable) (fun _ => num)
    overwritesInput shiftedLabels).isNone = true := by decide +kernel

example (x : Record.Input shiftedContext) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue C (Region.packedInputType shiftedContext.toList) x))
      (Program.ofCFGEntry shiftedTyped).code =
    LiveOut.observe model shiftedPorts shiftedFields shiftedCompiled.lowered.source x :=
  Materialize.packed_observe shiftedTyped model shiftedCompiled x ambient

example (x : Record.Input shiftedContext) (ambient : Env Runtime) :
    region model.raw (extend ambient (encodeValue C (Region.packedInputType shiftedContext.toList) x))
      (Program.ofCFGEntry shiftedTyped).code =
    region model.raw (extend ambient (encodeValue C (Region.packedInputType shiftedContext.toList) x))
      shiftedCompiled.admission.program.code :=
  Materialize.packed_roundTrip shiftedTyped model shiftedCompiled x ambient

private def shiftedInput (old middle chosen : Atom) (right : Bool) : Record.Input shiftedContext :=
  (((PUnit.unit, old), middle), if right then Sum.inr chosen else Sum.inl chosen)

private def number (x : Atom) : Value Runtime := .atom ⟨⟨()⟩, x⟩

private def shiftedPayload (old middle chosen : Atom) (right : Bool) : Value Runtime :=
  .pair (.pair (number chosen) (number (if right then old else middle))) (.pair (number middle) .unit)

open LambdaSSA.Semantics.Interaction (BlockInput splitTransfer) in
private theorem shifted_raw (old middle chosen : Atom) (right : Bool) :
    region model.raw (inputEnv shiftedContext (shiftedInput old middle chosen right)) shiftedLiveTable.erase =
      vis Event.choose (fun _ => pure (0, shiftedPayload old middle chosen right)) := by
  let env := inputEnv shiftedContext (shiftedInput old middle chosen right)
  let step (p : BlockInput Runtime 1) :=
    region model.raw (extend env p.2) (shiftedLiveTable.block p.1).erase >>=
      fun out => pure (splitTransfer 1 out)
  have entry : region model.raw env shiftedLiveTable.entry.erase =
      vis Event.choose (fun _ => pure (0, number old)) := by
    simp only [shiftedLiveTable, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
      LambdaSSA.Semantics.Interaction.term, pure_bind]
    let requested : ModelTree Event (Value Runtime) :=
      vis Event.choose (fun reply => pure (if reply then .inr (number old) else .inl (number old)))
    change ((requested >>= fun _ => pure (number old)) >>= fun v => pure (0, v)) = _
    simp only [requested, vis_bind, pure_bind]
  have row : step (0, number old) = pure (.inl (0, shiftedPayload old middle chosen right)) := by
    cases right <;>
      simp only [step, shiftedLiveTable, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase, region,
        LambdaSSA.Semantics.Interaction.term, pure_bind] <;>
      repeat' (first | rfl | erw [pure_bind])
  have loop : Silmaril.Elgot.iter step (0, number old) = pure (0, shiftedPayload old middle chosen right) := by
    rw [congrFun (Silmaril.Elgot.ITree.iterate_fixpoint step) (0, number old), row, pure_bind]
    rfl
  change (region model.raw env shiftedLiveTable.entry.erase >>= fun out =>
    Sum.elim pure (Silmaril.Elgot.iter step) (splitTransfer 1 out)) = _
  rw [entry, vis_bind]
  simp only [pure_bind]
  exact congrArg (vis Event.choose) (funext fun _ => loop)

example (old middle chosen : Atom) (right : Bool) :
    LiveOut.observe model shiftedPorts shiftedFields shiftedCompiled.lowered.source
      (shiftedInput old middle chosen right) =
      vis Event.choose (fun _ => pure (0, .inl (shiftedPayload old middle chosen right))) := by
  let x := shiftedInput old middle chosen right
  let ambient : Env Runtime := fun _ => .unit
  rw [← Materialize.packed_observe shiftedTyped model shiftedCompiled x ambient, ← inputEnv_packet]
  have contextTree := Capture.packed_context_tree model.raw shiftedTyped ambient (inputEnv shiftedContext x)
  change region model.raw (extend ambient (Capture.packEnv 3 (inputEnv shiftedContext x)))
    (Program.ofCFGEntry shiftedTyped).code = _
  rw [show region model.raw (extend ambient (Capture.packEnv 3 (inputEnv shiftedContext x)))
      (Program.ofCFGEntry shiftedTyped).code =
      (region model.raw (inputEnv shiftedContext x) shiftedLiveTable.erase >>= fun p =>
        pure (LambdaSSA.FiniteCFG.packedTreeOutput p)) from contextTree]
  rw [shifted_raw, vis_bind]
  simp only [pure_bind, LambdaSSA.FiniteCFG.packedTreeOutput, Region.packedExitValue]

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.Witnessed.Tests
