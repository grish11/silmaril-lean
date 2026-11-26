module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Packed.Institution.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.PackedInstitution

open CategoryTheory
open Silmaril.Logic.Institution (Room)
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.PackedInstitution

universe u v

variable {κ : Type (u + 1)} {P Q S : FlatInstitution.Signature.{u, v} κ} {A : Ty κ}

private theorem program_map_id {B : Ty κ} (p : Program P.Instr A B) :
    p.map Morphism.SignatureMap.id rfl = p := by
  cases p with
  | mk code typed =>
    simp only [Program.map, Program.mk.injEq]
    exact Region.mapInstr_id code

private theorem program_map_comp {B : Ty κ} (g : P ⟶ Q) (h : Q ⟶ S)
    (p : Program P.Instr A B) :
    p.map (g ≫ h).toSignatureMap (g ≫ h).types =
      (p.map g.toSignatureMap g.types).map h.toSignatureMap h.types := by
  simp only [Program.map, Program.mk.injEq]
  exact (Region.mapInstr_comp g.toSignatureMap.instr h.toSignatureMap.instr p.code).symm

theorem sentence_map_id (s : Sentence P A) : s.map (𝟙 P) = s := by
  cases s with
  | mk exits external left right =>
    exact congrArg₂ (Sentence.mk exits external) (program_map_id left) (program_map_id right)

theorem sentence_map_comp (g : P ⟶ Q) (h : Q ⟶ S) (s : Sentence P A) :
    s.map (g ≫ h) = (s.map g).map h := by
  cases s
  simp only [Sentence.map, program_map_comp]

theorem packSentence_map (g : P ⟶ Q) (s : FlatInstitution.Sentence P) :
    packSentence (s.map g) = (packSentence s).map g :=
  congrArg₂ (Sentence.mk s.exits s.external)
    (Program.ofCFG_mapInstr g.toSignatureMap g.types s.left.typed)
    (Program.ofCFG_mapInstr g.toSignatureMap g.types s.right.typed)

theorem packingCorridor_natural [AtomValues κ] (Events : Type u → Type u) (g : P ⟶ Q) :
    FlatInstitution.corridor Events g ≫ packingCorridor Events Q =
      packingCorridor Events P ≫ corridor Events g := by
  apply Room.hom_ext (funext (packSentence_map g))
  exact CategoryTheory.Functor.ext fun _ => rfl

private def unreachableLoop (P : FlatInstitution.Signature.{u, v} κ) : FiniteCFG P.Instr 1 1 0 :=
  ⟨.br 1 .unit, fun _ => .br 0 (.bv 0)⟩

private def loopTable (A : Ty κ) : FlatInstitution.Table P (fun _ : Fin 1 => Ty.unit) :=
  FlatInstitution.Table.ofTyped (a := unreachableLoop P) (R := fun _ => A)
    ⟨.br .unit, fun _ => .br .bv⟩

theorem packSentence_not_injective (P : FlatInstitution.Signature.{u, v} κ) :
    ¬ Function.Injective (packSentence (P := P)) := by
  let s : FlatInstitution.Sentence P := ⟨1, fun _ => .unit, loopTable .unit, loopTable .unit⟩
  let t : FlatInstitution.Sentence P := ⟨1, fun _ => .unit, loopTable .empty, loopTable .unit⟩
  intro inj
  have eq : s = t := inj (show packSentence s = packSentence t from rfl)
  have profile := congrArg (fun a : FlatInstitution.Sentence P =>
    List.ofFn a.left.internal) eq
  change [Ty.unit] = [Ty.empty] at profile
  cases profile

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.PackedInstitution
