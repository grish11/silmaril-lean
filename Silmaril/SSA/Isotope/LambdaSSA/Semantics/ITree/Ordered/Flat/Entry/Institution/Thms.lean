module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Entry.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Entry.Institution

/-! # Packing with external inputs as an institution comorphism -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.EntryInstitution

open CategoryTheory
open Silmaril.Logic.Institution (Room Inst)

universe u v

variable {κ : Type (u + 1)} {P Q S : FlatInstitution.Signature.{u, v} κ}
  {n exits : Nat} {β : BoundCtx (Ty κ) n} {D : Fin exits → Ty κ}

local notation "A" => Region.packedInputType β.toList

@[simp] theorem Table.map_id (a : Table P β D) : a.map (𝟙 P) = a :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.EntryInstitution.table_map_id a

theorem Table.map_comp (g : P ⟶ Q) (h : Q ⟶ S) (a : Table P β D) :
    a.map (g ≫ h) = (a.map g).map h :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.EntryInstitution.table_map_comp g h a

@[simp] theorem Sentence.map_id (s : Sentence P β) : s.map (𝟙 P) = s := by
  cases s
  simp only [Sentence.map, Table.map_id]

theorem Sentence.map_comp (g : P ⟶ Q) (h : Q ⟶ S) (s : Sentence P β) :
    s.map (g ≫ h) = (s.map g).map h := by
  cases s
  simp only [Sentence.map, Table.map_comp]

/-- The packing square is equality of syntax at the same entry type. -/
theorem packSentence_map (g : P ⟶ Q) (s : Sentence P β) :
    packSentence (s.map g) = (packSentence s).map g :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.EntryInstitution.packSentence_map g s

variable [AtomValues κ] (Events : Type u → Type u)

theorem satisfaction (g : P ⟶ Q) (M : Model (κ := κ) Events Q.Instr) (s : Sentence P β) :
    Satisfies Events M (s.map g) ↔ Satisfies Events (FlatInstitution.reduct Events g M) s :=
  (corridor Events β g).sat (Discrete.mk M) s

theorem packingCorridor_natural (g : P ⟶ Q) :
    corridor Events β g ≫ packingCorridor Events β Q =
      packingCorridor Events β P ≫ PackedInstitution.corridor Events g A :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.EntryInstitution.packingCorridor_natural Events g

theorem packing_satisfaction (M : Model (κ := κ) Events P.Instr) (s : Sentence P β) :
    (PackedInstitution.room Events P A).Sat (Discrete.mk M) (packSentence s) ↔ Satisfies Events M s :=
  (packingCorridor Events β P).sat (Discrete.mk M) s

theorem packing_entails_iff (Γ : Set (Sentence P β)) (φ : Sentence P β) :
    (room Events β P).Entails Γ φ ↔
      (PackedInstitution.room Events P A).Entails (packSentence '' Γ) (packSentence φ) :=
  (packingCorridor Events β P).entails_map_iff (fun M => ⟨M, rfl⟩) Γ φ

@[expose] def roomFunctor (β : BoundCtx (Ty κ) n) :
    FlatInstitution.Signature.{u, v} κ ⥤ Room.{max (u + 1) v, max (u + 1) v, max (u + 1) v} where
  obj := room Events β
  map g := corridor Events β g
  map_id P := Room.hom_ext (funext Sentence.map_id) (FlatInstitution.reductFunctor_id Events P)
  map_comp g h := Room.hom_ext (funext (Sentence.map_comp g h)) (FlatInstitution.reductFunctor_comp Events g h)

@[expose] def institution (κ : Type (u + 1)) [AtomValues κ] (β : BoundCtx (Ty κ) n) :
    Inst.{max (u + 1) (v + 1), max (u + 1) v, max (u + 1) v, max (u + 1) v, max (u + 1) v} :=
  ⟨FlatInstitution.Signature.{u, v} κ, roomFunctor Events β⟩

/-- Over the same primitive signatures and models, pack each table at its
shared external entry context. -/
@[expose] def packingComorphism (κ : Type (u + 1)) [AtomValues κ] (β : BoundCtx (Ty κ) n) :
    Inst.CoHom (institution.{u, v} Events κ β)
      (PackedInstitution.institution.{u, v} Events κ (Region.packedInputType β.toList)) where
  Φ := 𝟭 _
  ρ := { app := packingCorridor Events β, naturality := fun {_ _} g => packingCorridor_natural Events g }

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.EntryInstitution
