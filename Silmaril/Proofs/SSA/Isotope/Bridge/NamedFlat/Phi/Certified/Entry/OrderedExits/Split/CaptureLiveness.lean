module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.CaptureLiveness.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Thms
import Silmaril.SSA.LambdaRTL.CFG.Lexical.Thms
import Silmaril.SSA.LambdaRTL.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split

open Silmaril.Isotope
open Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry (Captures)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
  (profileCandidateFor_movedSlot_absent)
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Record (Input field inputEnv_field)

universe u v
variable {κ V W Reg K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context}

private theorem free_supported (a : Admission P I fields C) {reg : Option V × Nat}
    (used : reg ∈ (Versioning.compile (Phi.OrderedExits.lower a.source)).entry.toRegion.fv) :
    reg.1 ∈ Versioning.registers (Phi.OrderedExits.lower a.source) ∧ reg.2 = 0 := by
  have mem := Region.fv_subset_of_isSSA (Versioning.compile_entry_isSSA (Phi.OrderedExits.lower a.source)) used
  obtain ⟨name, member, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp mem)
  exact ⟨member, rfl⟩

section Semantics

variable [AtomValues κ] {Events : Type u → Type u}

theorem observe_eq_of_entryAgreement (a : Admission P I fields C)
    (M : LambdaSSA.Semantics.Interaction.Typed.Ordered.Model (κ := κ) Events P.Instr)
    (left right : Input I.context)
    (agrees : ∀ i, a.entryUsesSlot i → field I.context left i = field I.context right i) :
    a.observe M left = a.observe M right := by
  let model := treeModel M.raw
  let graph := Phi.OrderedExits.lower a.source
  let lexical := Versioning.compile graph
  let leftEnv := Phi.inputEnv model (C.store left)
  let rightEnv := Phi.inputEnv model (C.store right)
  have closed : RoundTrip.PacketClosedTable lexical.blocks := fun item member =>
    Region.fv_subset_of_isSSA (Versioning.compile_blocks_areSSA graph item member)
  have steps : stepSSA model lexical.blocks leftEnv = stepSSA model lexical.blocks rightEnv := by
    funext p
    exact (RoundTrip.step_packetClosed_obs model _ closed leftEnv (p.1, p.2, leftEnv)).symm.trans
      (RoundTrip.step_packetClosed_obs model _ closed rightEnv (p.1, p.2, leftEnv))
  have entry : lexical.entry.evalJump model leftEnv = lexical.entry.evalJump model rightEnv := by
    rw [CFG.Body.evalJump_eq_evalSSA, CFG.Body.evalJump_eq_evalSSA]
    apply Region.evalSSA_congr
    rintro ⟨key, version⟩ used
    have zero : version = 0 := (free_supported a used).2
    subst version
    cases key with
    | none => rfl
    | some name =>
      cases lookup : first C.names (some name) with
      | none =>
        simp [leftEnv, rightEnv, Phi.inputEnv, Phi.liftStore, Captures.store, NamedFlat.Entry.store, lookup]
      | some slot =>
        have named : C.names slot = some name := of_decide_eq_true
          (List.find?_some (p := fun i => decide (C.names i = some name)) (a := slot) lookup)
        have usedSlot : a.entryUsesSlot slot := by
          unfold Admission.entryUsesSlot
          rw [named]
          exact used
        have decoded : NamedFlat.Entry.inputEnv I.context left slot.val =
            NamedFlat.Entry.inputEnv I.context right slot.val := by
          rw [inputEnv_field, inputEnv_field, agrees slot usedSlot]
        simpa [leftEnv, rightEnv, Phi.inputEnv, Phi.liftStore, Captures.store, NamedFlat.Entry.store, lookup]
          using decoded
  have pairs : (treeModel M.raw).PairLawful := ⟨fun _ _ => rfl⟩
  rw [Admission.observe, Admission.observe,
    Phi.OrderedExits.run_commutes _ pairs a.source (C.store left),
    Phi.OrderedExits.run_commutes _ pairs a.source (C.store right)]
  change (runSSA model lexical leftEnv >>= _) = (runSSA model lexical rightEnv >>= _)
  rw [runSSA, runSSA, entry, steps]

end Semantics

theorem movedCaptureSlot_unused [DecidableEq W] (a : Admission P I fields C) (plan : Plan V W K K)
    {slot : Fin I.slots} (member : slot ∈ a.movedCaptureSlots plan) : ¬ a.entryUsesSlot slot := by
  unfold Admission.movedCaptureSlots at member
  cases result : a.splitProfile plan with
  | none => simp [result] at member
  | some candidate =>
    simp only [result, Option.map_some, Option.getD_some, List.mem_map] at member
    obtain ⟨⟨i, ty⟩, listed, rfl⟩ := member
    intro used
    have absent := profileCandidateFor_movedSlot_absent plan a.source (Phi.OrderedExits.lower a.source)
      (Phi.OrderedExits.lower (plan.rewrite a.source)) C.names a.internal result listed
    exact absent (free_supported a used).1

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split
