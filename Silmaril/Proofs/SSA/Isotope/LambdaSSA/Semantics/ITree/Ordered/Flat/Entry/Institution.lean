module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Entry.Institution.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.EntryInstitution

open CategoryTheory
open Silmaril.Logic.Institution (Room)
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.EntryInstitution

universe u v

variable {κ : Type (u + 1)} {P Q S : FlatInstitution.Signature.{u, v} κ}
  {n exits : Nat} {β : BoundCtx (Ty κ) n} {D : Fin exits → Ty κ}

private theorem table_congr {blocks : Nat} {R : Fin blocks → Ty κ}
    {a b : FiniteCFG P.Instr blocks exits n} (eq : a = b)
    (ha : a.HasType β R D) (hb : b.HasType β R D) :
    Table.ofTyped (P := P) ha = Table.ofTyped hb := by
  subst b
  rfl

theorem table_map_id (a : Table P β D) : a.map (𝟙 P) = a := by
  cases a with
  | mk blocks R code typed =>
    exact table_congr (FiniteCFG.mapInstr_id code) _ _

theorem table_map_comp (g : P ⟶ Q) (h : Q ⟶ S) (a : Table P β D) :
    a.map (g ≫ h) = (a.map g).map h :=
  table_congr (FiniteCFG.mapInstr_comp g.toSignatureMap.instr h.toSignatureMap.instr a.code).symm _ _

theorem packSentence_map (g : P ⟶ Q) (s : Sentence P β) :
    packSentence (s.map g) = (packSentence s).map g :=
  congrArg₂ (PackedInstitution.Sentence.mk s.exits s.external)
    (Program.ofCFGEntry_mapInstr g.toSignatureMap g.types s.left.typed)
    (Program.ofCFGEntry_mapInstr g.toSignatureMap g.types s.right.typed)

theorem packingCorridor_natural [AtomValues κ] (Events : Type u → Type u) (g : P ⟶ Q) :
    corridor Events β g ≫ packingCorridor Events β Q =
      packingCorridor Events β P ≫ PackedInstitution.corridor Events g (Region.packedInputType β.toList) :=
  Room.hom_ext (funext (packSentence_map g)) (CategoryTheory.Functor.ext fun _ => rfl)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.EntryInstitution
