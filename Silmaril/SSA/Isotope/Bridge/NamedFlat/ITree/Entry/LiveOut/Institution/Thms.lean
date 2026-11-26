module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOutInstitution

/-! # Ordered satisfaction under primitive relabelling -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut

open CategoryTheory
open Silmaril.Logic.Institution (Room Inst)
open Silmaril.SSA.LambdaRTL
open LambdaSSA (Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (TraceLE)

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P Q S : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)}

local notation "A" => Region.packedInputType I.context.toList

@[simp] theorem Admitted.map_id (a : Admitted P I fields) : a.map (𝟙 P) = a :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.admitted_map_id a

theorem Admitted.map_comp (a : Admitted P I fields) (g : P ⟶ Q) (h : Q ⟶ S) :
    a.map (g ≫ h) = (a.map g).map h :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.admitted_map_comp a g h

@[simp] theorem Sentence.map_id (s : Sentence P I fields) : s.map (𝟙 P) = s :=
  Prod.ext s.1.map_id s.2.map_id

theorem Sentence.map_comp (s : Sentence P I fields) (g : P ⟶ Q) (h : Q ⟶ S) :
    s.map (g ≫ h) = (s.map g).map h :=
  Prod.ext (s.1.map_comp g h) (s.2.map_comp g h)

/-- Relabel the same typed program at the original exit field order. -/
theorem Admission.program_map {source : CFG V K P.Instr} (a : Admission P I fields source) (g : P ⟶ Q) :
    (a.map g).program = a.program.map g.toSignatureMap g.types :=
  Program.ofCFGEntry_mapInstr g.toSignatureMap g.types a.rtl.versioned.table.typed

theorem toPacked_map (s : Sentence P I fields) (g : P ⟶ Q) :
    toPacked (s.map g) = (toPacked s).map g :=
  congrArg₂ (PackedInstitution.Sentence.mk I.exits.length (exitInterface I fields).external)
    (s.1.certificate.program_map g) (s.2.certificate.program_map g)

variable [AtomValues κ] {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)

/-- This equality compares the original mutable runners at the same typed
input record. The signature map leaves the exit projection fixed. -/
theorem observe_mapOp (g : P ⟶ Q) (M : Model (κ := κ) Events Q.Instr)
    (source : CFG V K P.Instr) (x : Ty.denote C A) :
    observe M I fields (source.mapOp g.toSignatureMap.instr) x =
      observe (FlatInstitution.reduct Events g M) I fields source x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.observe_mapOp g M source x

theorem satisfaction (g : P ⟶ Q) (M : Model (κ := κ) Events Q.Instr) (s : Sentence P I fields) :
    Satisfies M (s.map g) ↔ Satisfies (FlatInstitution.reduct Events g M) s :=
  forall_congr' fun x => by
    change TraceLE (observe M I fields (s.1.source.mapOp g.toSignatureMap.instr) x)
      (observe M I fields (s.2.source.mapOp g.toSignatureMap.instr) x) ↔ _
    rw [observe_mapOp g M s.1.source, observe_mapOp g M s.2.source]

theorem toRTL_satisfies_iff (M : Model (κ := κ) Events P.Instr) (s : Sentence P I fields) :
    rtlSatisfies M (toRTL s) ↔ Satisfies M s :=
  forall_congr' fun x => by
    change TraceLE (s.1.certificate.rtl.observe M x) (s.2.certificate.rtl.observe M x) ↔ _
    rw [s.1.certificate.observe_rtl M x, s.2.certificate.observe_rtl M x]

theorem toPacked_satisfies_iff (M : Model (κ := κ) Events P.Instr) (s : Sentence P I fields) :
    (PackedInstitution.room Events P A).Sat (Discrete.mk M) (toPacked s) ↔ Satisfies M s :=
  satisfies_iff M s.1.certificate s.2.certificate (fun _ => .unit)

theorem toPacked_satisfies_map_iff (g : P ⟶ Q) (M : Model (κ := κ) Events Q.Instr)
    (s : Sentence P I fields) :
    (PackedInstitution.room Events Q A).Sat (Discrete.mk M) ((toPacked s).map g) ↔
      Satisfies (FlatInstitution.reduct Events g M) s := by
  rw [← toPacked_map, toPacked_satisfies_iff, satisfaction]

variable (I fields Events) in
def corridor (g : P ⟶ Q) : room I fields Events P ⟶ room I fields Events Q where
  sen s := s.map g
  mod := FlatInstitution.reductFunctor Events g
  sat M s := satisfaction g M.as s

variable (I fields Events) in
def attachmentCorridor (P : FlatInstitution.Signature.{u, v} κ) :
    room I fields Events P ⟶ rtlRoom (exitInterface I fields) Events P :=
  ⟨toRTL, 𝟭 _, fun M s => toRTL_satisfies_iff M.as s⟩

theorem attachmentCorridor_natural (g : P ⟶ Q) :
    corridor I fields Events g ≫ attachmentCorridor I fields Events Q =
      attachmentCorridor I fields Events P ≫ rtlCorridor (exitInterface I fields) Events g :=
  Room.hom_ext rfl (CategoryTheory.Functor.ext fun _ => rfl)

variable (I fields Events) in
/-- A fixed live-out interface over the existing primitive signature category. -/
def institution :
    Inst.{max (u + 1) (v + 1), max (u + 1) v, max (u + 1) v, max (u + 1) v, max (u + 1) v} :=
  ⟨FlatInstitution.Signature.{u, v} κ, {
    obj := room I fields Events
    map g := corridor I fields Events g
    map_id P := Room.hom_ext (funext Sentence.map_id) (FlatInstitution.reductFunctor_id Events P)
    map_comp g h := Room.hom_ext (funext fun s => s.map_comp g h)
      (FlatInstitution.reductFunctor_comp Events g h) }⟩

variable (I fields Events) in
def attachmentComorphism : Inst.CoHom (institution.{u, v} I fields Events)
    (rtlInstitution.{u, v} (exitInterface I fields) Events) :=
  ⟨𝟭 _, {
    app := attachmentCorridor I fields Events
    naturality := fun {_ _} g => attachmentCorridor_natural g }⟩

variable (I fields Events) in
/-- Attach the projection, then use the existing named-to-packed map. -/
def packedComorphism : Inst.CoHom (institution.{u, v} I fields Events)
    (PackedInstitution.institution.{u, v} Events κ A) :=
  (attachmentComorphism I fields Events).comp (packedRTLComorphism (exitInterface I fields) Events)

theorem packedComorphism_sentence (s : Sentence P I fields) :
    ((packedComorphism I fields Events).ρ.app P).sen s = toPacked s :=
  rfl

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut
