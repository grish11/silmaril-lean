module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Institution.Thms

/-! # A write-only register becomes observable through the generated packet -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.Examples

open Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree HasTrace Trace TraceLE iterate_fixpoint out_ret
  vis vis_bind diverge hasTrace_vis_exchange_iff)
open Silmaril.Isotope.Morphism (SignatureMap)
open CategoryTheory

private abbrev SortName := ULift.{1} Unit
private abbrev Reg := ULift.{1} (Fin 4)
private abbrev Label := ULift.{1} (Fin 2)
private abbrev Event (_ : Type) := Empty
private abbrev Atom := ULift.{1} Nat

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private instance : HasTy Empty (Ty SortName) := ⟨Empty.elim, Empty.elim⟩
private instance : HasEff Empty Bool := ⟨Empty.elim⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Empty

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event signature.Instr where
  instructions :=
    { denote := fun f => Empty.elim f
      denotePure := fun f => Empty.elim f
      denote_pure := fun f => Empty.elim f }
  raw := Empty.elim
  compatible := fun f => Empty.elim f

private def left : Reg := ⟨0⟩
private def right : Reg := ⟨1⟩
private def saved : Reg := ⟨2⟩
private def param : Reg := ⟨3⟩
private def blockLabel : Label := ⟨0⟩
private def exitLabel : Label := ⟨1⟩
private def num : Ty SortName := .base ⟨()⟩

private def names (i : Fin 2) : Reg := if i = 0 then right else left

private def ports : Interface SortName Reg Label :=
  ⟨2, .snoc (.snoc .nil num) num, names,
    (show ∀ i j : Fin 2, names i = names j → i = j from by decide),
    [exitLabel], fun _ => .unit⟩

private def fields (_ : Label) : List (Reg × Ty SortName) := [(saved, num)]

private def exitBlocks {F : Type} : List (Label × CFG.Block Reg Label F) :=
  [(blockLabel, ⟨param, .term (.br exitLabel .unit)⟩)]

private def source (read : Reg) : CFG Reg Label signature.Instr :=
  ⟨.let1 saved (.val (.var read)) (.term (.br blockLabel .unit)), exitBlocks⟩

-- The added exit read is across an internal transfer. It requires the
-- versioned edge packet to carry a register the old syntax only writes.
example : (CFG.Cyclic.Versioning.registers (source left)).contains saved = false := by decide

example : (CFG.Cyclic.Versioning.registers
    (CFG.Cyclic.LiveOut.attach (fun _ => [saved]) (source left))).contains saved = true := by decide

private def edgeType : Ty SortName := .product .unit (.product num (.product num .unit))

private def leftProgram : Admission signature ports fields (source left) :=
  (admit (P := signature) ports fields (source left) (fun _ => edgeType)).get (by decide)

private def rightProgram : Admission signature ports fields (source right) :=
  (admit (P := signature) ports fields (source right) (fun _ => edgeType)).get (by decide)

-- The same executable checker rejects an incorrect declared field type.
example : (admit (P := signature) ports (fun _ => [(saved, Ty.unit)])
    (source left) (fun _ => edgeType)).isNone = true := by decide

private abbrev Input := Ty.denote (AtomValues.carrier (κ := SortName))
  (LambdaSSA.Region.packedInputType ports.context.toList)

private def sample : Input := ((PUnit.unit, ⟨7⟩), ⟨9⟩)
private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩
private def ambient : Env Runtime := fun _ => .unit

private def inputStore (x : Input) : Reg → Value Runtime := store ports.names ports.context x

private def afterWrite (read : Reg) (x : Input) : Reg → Value Runtime :=
  upd (inputStore x) saved (inputStore x read)

private theorem run_jump {F : Type} {E : Type → Type}
    (m : Silmaril.SSA.LambdaRTL.Model F (fun A : Type 1 => Tree E A) (Value Runtime))
    (env : Reg → Value Runtime) :
    iter (CFG.Cyclic.step m exitBlocks) (blockLabel, .unit, env) =
      pure (exitLabel, m.unit, upd env param .unit) := by
  let step := CFG.Cyclic.step m exitBlocks
  let start : CFG.Cyclic.Transfer Reg Label (Value Runtime) := (blockLabel, .unit, env)
  let finish : CFG.Cyclic.Transfer Reg Label (Value Runtime) := (exitLabel, m.unit, upd env param .unit)
  change iter step start = pure finish
  rw [congrFun (iterate_fixpoint step) start]
  rw [show step start = pure (.inr finish) from rfl, pure_bind]
  change iter step finish = pure finish
  rw [congrFun (iterate_fixpoint step) finish]
  rw [show step finish = pure (.inl finish) from rfl, pure_bind]
  rfl

private theorem run_source (read : Reg) (x : Input) :
    CFG.Cyclic.run (treeModel model.raw) (source read) (inputStore x) =
      pure (exitLabel, .unit, upd (afterWrite read x) param .unit) := by
  change (pure (inputStore x read) >>= fun v =>
    iter (CFG.Cyclic.step (treeModel model.raw) exitBlocks)
      (blockLabel, .unit, upd (inputStore x) saved v)) = _
  rw [pure_bind, run_jump]
  rfl

-- The existing forgetful observation has the same exit and old payload for
-- every supplied record, even though the two assignments differ.
example (x : Input) :
    obs <$> CFG.Cyclic.run (treeModel model.raw) (source left) (inputStore x) =
      obs <$> CFG.Cyclic.run (treeModel model.raw) (source right) (inputStore x) := by
  simp only [run_source, map_pure, obs]

private def result (n : Nat) : Transfer Runtime :=
  (0, .inl (.pair .unit (.pair (atom n) .unit)))

private theorem left_observation : observe (P := signature) model ports fields (source left) sample =
    pure (result 7) := by
  change (CFG.Cyclic.run (treeModel model.raw) (source left) (inputStore sample) >>= _) = _
  rw [run_source, pure_bind]
  rfl

private theorem right_observation : observe (P := signature) model ports fields (source right) sample =
    pure (result 9) := by
  change (CFG.Cyclic.run (treeModel model.raw) (source right) (inputStore sample) >>= _) = _
  rw [run_source, pure_bind]
  rfl

private def encodedSample : Value Runtime :=
  encodeValue (AtomValues.carrier (κ := SortName)) (LambdaSSA.Region.packedInputType ports.context.toList) sample

example : region model.raw (extend ambient encodedSample) leftProgram.program.code = pure (result 7) :=
  (leftProgram.packed_tree model sample ambient).trans left_observation

example : region model.raw (extend ambient encodedSample) rightProgram.program.code = pure (result 9) :=
  (rightProgram.packed_tree model sample ambient).trans right_observation

example : ¬ model.Satisfies leftProgram.program rightProgram.program := by
  intro sat
  have h := ((satisfies_iff model leftProgram rightProgram ambient).mp sat) sample
  have distinct : ¬ TraceLE (pure (result 7) : Tree Event (Transfer Runtime)) (pure (result 9)) := by
    intro order
    have bad := order (.result (result 7)) (out_ret _)
    have tagged := (out_ret (E := Event) (result 9)).symm.trans bad
    have eq := Silmaril.Elgot.ITree.Visible.ret.inj (Part.some_inj.mp tagged)
    simp [result, atom] at eq
    exact (by decide : (9 : Nat) ≠ 7) (congrArg ULift.down eq)
  rw [left_observation, right_observation] at h
  exact distinct h

/-! ## A noninjective opcode map preserves the ordered exit record -/

private inductive Opcode
  | first
  | second
  | merged

private inductive ReadEvent : Type → Type
  | read (op : Opcode) (n : Nat) : ReadEvent Nat

private instance : HasTy Opcode (Ty SortName) := ⟨fun _ => num, fun _ => num⟩
private instance : HasEff Opcode Bool := ⟨fun _ => true⟩

private def effectSignature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Opcode

private def readRaw : Opcode → Value Runtime → Tree ReadEvent (Value Runtime)
  | op, .atom a => vis (.read op a.2.down) (fun reply => pure (atom reply))
  | _, _ => diverge

private def readModel : Model (κ := SortName) ReadEvent effectSignature.Instr where
  instructions :=
    { denote := fun op x => vis (.read op x.down) (fun reply => pure (ULift.up reply))
      denotePure := fun _ h => Bool.noConfusion h
      denote_pure := fun _ h => Bool.noConfusion h }
  raw := readRaw
  compatible := by
    dsimp only
    intro op x
    change vis (.read op x.down) (fun reply => pure (atom reply)) =
      ((vis (.read op x.down) (fun reply => pure (ULift.up reply)) : Tree ReadEvent Atom) >>=
        fun a => pure (atom a.down))
    simp only [vis_bind, pure_bind]

private def relabel : SignatureMap Opcode Opcode (Ty SortName) (Ty SortName) Bool Bool where
  instr _ := .merged
  ty := id
  eff := id
  source _ := rfl
  target _ := rfl
  effect _ := rfl

private def mergeOpcodes : effectSignature ⟶ effectSignature := ⟨relabel, rfl, rfl⟩

example : ¬ Function.Injective relabel.instr := by
  intro inj
  cases inj (show relabel.instr .first = relabel.instr .second from rfl)

private def effectSource (op : Opcode) (overwrite : Bool) : CFG Reg Label effectSignature.Instr :=
  let jump : CFG.Body Reg Label Opcode := .term (.br blockLabel .unit)
  ⟨.let1 saved (.app op (.var left))
    (if overwrite then .let1 saved (.val (.var left)) jump else jump), exitBlocks⟩

private def effectFields (_ : Label) : List (Reg × Ty SortName) :=
  [(saved, num), (left, num)]

private def effectResult (n : Nat) : Transfer Runtime :=
  (0, .inl (.pair .unit (.pair (atom n) (.pair (atom 7) .unit))))

private def keepsReply : Admission effectSignature ports effectFields (effectSource .first false) :=
  (admit (P := effectSignature) ports effectFields (effectSource .first false) (fun _ => edgeType)).get (by decide)

private def overwritesReply : Admission effectSignature ports effectFields (effectSource .second true) :=
  (admit (P := effectSignature) ports effectFields (effectSource .second true) (fun _ => edgeType)).get (by decide)

-- This renamed fixture independently passes at the same block profile.
example : (admit (P := effectSignature) ports effectFields
    ((effectSource .first false).mapOp relabel.instr) (fun _ => edgeType)).isSome = true := by decide

private theorem effect_observation (overwrite : Bool) :
    observe (P := effectSignature) readModel ports effectFields (effectSource .merged overwrite) sample =
      vis (.read .merged 7) (fun reply => pure (effectResult (if overwrite then 7 else reply))) := by
  cases overwrite
  · change (((vis (.read .merged 7) (fun reply => pure (atom reply)) : Tree ReadEvent (Value Runtime)) >>=
        fun v => iter (CFG.Cyclic.step (treeModel readModel.raw) exitBlocks)
          (blockLabel, .unit, upd (inputStore sample) saved v)) >>= _) = _
    simp only [vis_bind, pure_bind, run_jump]
    rfl
  · change (((vis (.read .merged 7) (fun reply => pure (atom reply)) : Tree ReadEvent (Value Runtime)) >>=
        fun v => pure (inputStore sample left) >>= fun original =>
          iter (CFG.Cyclic.step (treeModel readModel.raw) exitBlocks)
            (blockLabel, .unit, upd (upd (inputStore sample) saved v) saved original)) >>= _) = _
    simp only [vis_bind, pure_bind, run_jump]
    rfl

private def replyTrace : Trace ReadEvent (Transfer Runtime) :=
  .exchange (.read .merged 7) 11 (.result (effectResult 11))

private theorem keeps_trace :
    HasTrace (observe (P := effectSignature) readModel ports effectFields (effectSource .merged false) sample)
      replyTrace := by
  rw [effect_observation]
  simp only [replyTrace, hasTrace_vis_exchange_iff]
  exact out_ret _

example :
    HasTrace (region readModel.raw (extend ambient encodedSample)
      (keepsReply.map mergeOpcodes).program.code) replyTrace :=
  ((keepsReply.map mergeOpcodes).packed_tree readModel sample ambient).symm ▸ keeps_trace

private def comparison : Sentence effectSignature ports effectFields :=
  (⟨effectSource .first false, keepsReply⟩, ⟨effectSource .second true, overwritesReply⟩)

private theorem mapped_not_satisfied : ¬ Satisfies readModel (comparison.map mergeOpcodes) := by
  intro h
  have order := h sample
  change TraceLE (observe (P := effectSignature) readModel ports effectFields (effectSource .merged false) sample)
    (observe (P := effectSignature) readModel ports effectFields (effectSource .merged true) sample) at order
  have bad := order replyTrace keeps_trace
  rw [effect_observation] at bad
  simp only [replyTrace, hasTrace_vis_exchange_iff, HasTrace] at bad
  have eq := Silmaril.Elgot.ITree.Visible.ret.inj (Part.some_inj.mp ((out_ret (E := ReadEvent)
    (effectResult 7)).symm.trans bad))
  simp [effectResult, atom] at eq
  exact (by decide : (7 : Nat) ≠ 11) (congrArg ULift.down eq)

private abbrev packed := packedComorphism.{0, 0} ports effectFields ReadEvent
private abbrev renamed := (institution.{0, 0} ports effectFields ReadEvent).I.map mergeOpcodes

-- After merging the opcodes, the programs agree on the request and reply.
-- The final store projection distinguishes their packed results at reply 11.
example :
    ¬ (PackedInstitution.room ReadEvent effectSignature
        (LambdaSSA.Region.packedInputType ports.context.toList)).Sat (Discrete.mk readModel)
      ((packed.ρ.app effectSignature).sen (renamed.sen comparison)) :=
  fun h => mapped_not_satisfied ((packed.satisfaction effectSignature (Discrete.mk readModel) _).mp h)

example : ¬ Satisfies (FlatInstitution.reduct ReadEvent mergeOpcodes readModel) comparison :=
  fun h => mapped_not_satisfied ((satisfaction mergeOpcodes readModel comparison).mpr h)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.Examples
