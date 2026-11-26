module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Institution

/-! # Exact ordered observations of admitted named SSA and RTL -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry

open CategoryTheory
open Silmaril.Logic.Institution (Room Inst)
open Silmaril.SSA.LambdaRTL
open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v
variable {κ : Type (u + 1)} {V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P Q S : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}

@[simp] theorem SSA.map_id (a : SSA P I) : a.map (𝟙 P) = a :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.ssa_map_id a

theorem SSA.map_comp (f : P ⟶ Q) (g : Q ⟶ S) (a : SSA P I) : a.map (f ≫ g) = (a.map f).map g :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.ssa_map_comp f g a

@[simp] theorem RTL.map_id (a : RTL P I) : a.map (𝟙 P) = a :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.rtl_map_id a

theorem RTL.map_comp (f : P ⟶ Q) (g : Q ⟶ S) (a : RTL P I) : a.map (f ≫ g) = (a.map f).map g :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.rtl_map_comp f g a

variable [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType I.context.toList
local notation "C" => AtomValues.carrier (κ := κ)

/-- The whole weak tree at the supplied typed record agrees with the actual
lexical runner after tagging its external return. -/
theorem SSA.observe_tree (M : Model (κ := κ) Events P.Instr) (a : SSA P I)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    a.observe M x = region M.raw (extend ambient (encodeValue C A x))
      (Program.ofCFGEntry a.table.typed).code :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.ssa_observe_tree M a x ambient

/-- The checked input store is also the version-zero projection required by
the existing lawful Elgot versioning theorem. -/
theorem RTL.observe_version (M : Model (κ := κ) Events P.Instr) (a : RTL P I)
    (x : Ty.denote C A) : a.observe M x = a.versioned.observe M x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.rtl_observe_version M a x

theorem toSSA_satisfies_iff (M : Model (κ := κ) Events P.Instr) (s : RTLSentence P I) :
    ssaSatisfies M (toSSA s) ↔ rtlSatisfies M s := by
  simp only [ssaSatisfies, rtlSatisfies, toSSA, RTL.observe_version]
  rfl

theorem toFlat_satisfies_iff (M : Model (κ := κ) Events P.Instr) (s : SSASentence P I) :
    EntryInstitution.Satisfies Events M (toFlat s) ↔ ssaSatisfies M s :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.toFlat_satisfies_iff M s

/-- The composed direction uses the same model on both sides. -/
theorem toPacked_satisfies_iff (M : Model (κ := κ) Events P.Instr) (s : RTLSentence P I) :
    (PackedInstitution.room Events P A).Sat (Discrete.mk M)
      (EntryInstitution.packSentence (toFlat (I := I.version) (toSSA s))) ↔ rtlSatisfies M s :=
  (EntryInstitution.packing_satisfaction Events M _).trans
    ((toFlat_satisfies_iff (I := I.version) M _).trans (toSSA_satisfies_iff M s))

variable (I) (Events) in
/-- The named lexical room has exactly the typed weak-tree models of the flat room. -/
def ssaRoom (P : FlatInstitution.Signature.{u, v} κ) :
    Room.{max (u + 1) v, max (u + 1) v, max (u + 1) v} where
  Sen := SSASentence P I
  Mod := (EntryInstitution.room Events I.context P).Mod
  Sat M s := ssaSatisfies M.as s

variable (I) (Events) in
def rtlRoom (P : FlatInstitution.Signature.{u, v} κ) :
    Room.{max (u + 1) v, max (u + 1) v, max (u + 1) v} where
  Sen := RTLSentence P I
  Mod := (EntryInstitution.room Events I.context P).Mod
  Sat M s := rtlSatisfies M.as s

variable (I) (Events) in
def ssaCorridor (g : P ⟶ Q) : ssaRoom I Events P ⟶ ssaRoom I Events Q where
  sen s := (s.1.map g, s.2.map g)
  mod := FlatInstitution.reductFunctor Events g
  sat M s := (toFlat_satisfies_iff M.as _).symm.trans
    ((EntryInstitution.satisfaction Events g M.as (toFlat s)).trans (toFlat_satisfies_iff _ _))

variable (I) (Events) in
def rtlCorridor (g : P ⟶ Q) : rtlRoom I Events P ⟶ rtlRoom I Events Q where
  sen s := (s.1.map g, s.2.map g)
  mod := FlatInstitution.reductFunctor Events g
  sat M s := (toSSA_satisfies_iff M.as _).symm.trans
    (((ssaCorridor I.version Events g).sat M (toSSA s)).trans (toSSA_satisfies_iff _ _))

variable (I) (Events) in
def elaborateCorridor (P : FlatInstitution.Signature.{u, v} κ) :
    ssaRoom I Events P ⟶ EntryInstitution.room Events I.context P :=
  ⟨toFlat, 𝟭 _, fun M s => toFlat_satisfies_iff M.as s⟩

variable (I) (Events) in
def versionCorridor (P : FlatInstitution.Signature.{u, v} κ) :
    rtlRoom I Events P ⟶ ssaRoom I.version Events P :=
  ⟨toSSA, 𝟭 _, fun M s => toSSA_satisfies_iff M.as s⟩

theorem elaborateCorridor_natural (g : P ⟶ Q) :
    ssaCorridor I Events g ≫ elaborateCorridor I Events Q =
      elaborateCorridor I Events P ≫ EntryInstitution.corridor Events I.context g :=
  Room.hom_ext rfl (CategoryTheory.Functor.ext fun _ => rfl)

theorem versionCorridor_natural (g : P ⟶ Q) :
    rtlCorridor I Events g ≫ versionCorridor I Events Q =
      versionCorridor I Events P ≫ ssaCorridor I.version Events g :=
  Room.hom_ext rfl (CategoryTheory.Functor.ext fun _ => rfl)

variable (I) (Events) in
def ssaInstitution :
    Inst.{max (u + 1) (v + 1), max (u + 1) v, max (u + 1) v, max (u + 1) v, max (u + 1) v} :=
  ⟨FlatInstitution.Signature.{u, v} κ, {
    obj := ssaRoom I Events
    map g := ssaCorridor I Events g
    map_id P := Room.hom_ext (funext fun s => Prod.ext (SSA.map_id s.1) (SSA.map_id s.2))
      (FlatInstitution.reductFunctor_id Events P)
    map_comp g h := Room.hom_ext (funext fun s => Prod.ext (SSA.map_comp g h s.1) (SSA.map_comp g h s.2))
      (FlatInstitution.reductFunctor_comp Events g h) }⟩

variable (I) (Events) in
def rtlInstitution :
    Inst.{max (u + 1) (v + 1), max (u + 1) v, max (u + 1) v, max (u + 1) v, max (u + 1) v} :=
  ⟨FlatInstitution.Signature.{u, v} κ, {
    obj := rtlRoom I Events
    map g := rtlCorridor I Events g
    map_id P := Room.hom_ext (funext fun s => Prod.ext (RTL.map_id s.1) (RTL.map_id s.2))
      (FlatInstitution.reductFunctor_id Events P)
    map_comp g h := Room.hom_ext (funext fun s => Prod.ext (RTL.map_comp g h s.1) (RTL.map_comp g h s.2))
      (FlatInstitution.reductFunctor_comp Events g h) }⟩

variable (I) (Events) in
/-- Elaborate the actual admitted lexical programs over the same signatures. -/
def elaborateComorphism : Inst.CoHom (ssaInstitution.{u, v} I Events)
    (EntryInstitution.institution.{u, v} Events κ I.context) :=
  ⟨𝟭 _, { app := elaborateCorridor I Events, naturality := fun {_ _} g => elaborateCorridor_natural g }⟩

variable (I) (Events) in
/-- Connect checked mutable sources to their actual certified versioner output. -/
def versionComorphism : Inst.CoHom (rtlInstitution.{u, v} I Events)
    (ssaInstitution.{u, v} I.version Events) :=
  ⟨𝟭 _, { app := versionCorridor I Events, naturality := fun {_ _} g => versionCorridor_natural g }⟩

variable (I) (Events) in
def packedSSAComorphism : Inst.CoHom (ssaInstitution.{u, v} I Events)
    (PackedInstitution.institution.{u, v} Events κ A) :=
  (elaborateComorphism I Events).comp (EntryInstitution.packingComorphism Events κ I.context)

variable (I) (Events) in
def packedRTLComorphism : Inst.CoHom (rtlInstitution.{u, v} I Events)
    (PackedInstitution.institution.{u, v} Events κ A) :=
  (versionComorphism I Events).comp (packedSSAComorphism I.version Events)

end Silmaril.Isotope.Bridge.NamedFlat.Entry
