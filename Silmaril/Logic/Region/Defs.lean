module

public import Silmaril.Semantics.Region.Defs
public import Mathlib.Data.Finset.Image
public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-! # The raw region-relation institution

Signatures name the four carriers. Morphisms map their names (including
identifications); sentences are ground raw judgments and Boolean combinations.
Models are arbitrary raw bundles, with a discrete category of models. Reduct
is pi-style precomposition, including finite images of supports and exits.
This institution says nothing about operational soundness or gluing.
Existentially erased judgments are deliberately not sentences: a reduct need
not see every segment witness in the target signature.
-/

@[expose] public section
namespace Silmaril.Logic.Region
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Semantics.Region

structure Signature where
  Img : Type
  Assum : Type
  Seg : Type
  Lab : Type

@[ext] structure Signature.Hom (A B : Signature) where
  image : A.Img → B.Img
  iface : A.Assum → B.Assum
  segment : A.Seg → B.Seg
  label : A.Lab → B.Lab

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨id, id, id, id⟩
  comp f g := ⟨g.image ∘ f.image, g.iface ∘ f.iface, g.segment ∘ f.segment, g.label ∘ f.label⟩

inductive Sentence (A : Signature) where
  | segBB (image : A.Img) (iface : A.Assum) (segment : A.Seg)
  | bb (image : A.Img) (iface : A.Assum) (segment : A.Seg) (entry : A.Lab) (exits : Finset A.Lab)
  | sr (image : A.Img) (iface : A.Assum) (support : Finset A.Seg) (entry exit : A.Lab)
  | optional (image : A.Img) (iface : A.Assum) (support : Finset A.Seg)
      (entry : A.Lab) (exit : Option A.Lab)
  | reg (image : A.Img) (iface : A.Assum) (support : Finset A.Seg) (entry : A.Lab) (exits : Finset A.Lab)
  | neg (p : Sentence A)
  | conj (p q : Sentence A)

noncomputable def Sentence.map {A B : Signature} (f : A ⟶ B) : Sentence A → Sentence B :=
  open Classical in fun s => match s with
  | .segBB i a seg => .segBB (f.image i) (f.iface a) (f.segment seg)
  | .bb i a seg e xs => .bb (f.image i) (f.iface a) (f.segment seg) (f.label e) (xs.image f.label)
  | .sr i a ss e x => .sr (f.image i) (f.iface a) (ss.image f.segment) (f.label e) (f.label x)
  | .optional i a ss e x =>
      .optional (f.image i) (f.iface a) (ss.image f.segment) (f.label e) (x.map f.label)
  | .reg i a ss e xs =>
      .reg (f.image i) (f.iface a) (ss.image f.segment) (f.label e) (xs.image f.label)
  | .neg p => .neg (p.map f)
  | .conj p q => .conj (p.map f) (q.map f)

abbrev Model (A : Signature) := SegmentRegionModel A.Img A.Assum A.Seg A.Lab

noncomputable def reduct {A B : Signature} (f : A ⟶ B) (M : Model B) : Model A :=
  open Classical in {
    SegBB := fun i a s => M.SegBB (f.image i) (f.iface a) (f.segment s)
    BB := fun i a s e xs => M.BB (f.image i) (f.iface a) (f.segment s) (f.label e) (xs.image f.label)
    SR := fun i a ss e x => M.SR (f.image i) (f.iface a) (ss.image f.segment) (f.label e) (f.label x)
    SR' := fun i a ss e x => M.SR' (f.image i) (f.iface a) (ss.image f.segment) (f.label e) (x.map f.label)
    Reg := fun i a ss e xs => M.Reg (f.image i) (f.iface a) (ss.image f.segment) (f.label e) (xs.image f.label) }

def Sat {A : Signature} (M : Model A) : Sentence A → Prop
  | .segBB i a s => M.SegBB i a s
  | .bb i a s e xs => M.BB i a s e xs
  | .sr i a ss e x => M.SR i a ss e x
  | .optional i a ss e x => M.SR' i a ss e x
  | .reg i a ss e xs => M.Reg i a ss e xs
  | .neg p => ¬ Sat M p
  | .conj p q => Sat M p ∧ Sat M q
end Silmaril.Logic.Region
