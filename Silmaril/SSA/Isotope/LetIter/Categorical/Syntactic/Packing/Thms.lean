module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.Packing

/-! # Packed native LetIter reification -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Thesis.LambdaIter (Sig)
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType)
open Silmaril.Thesis.LambdaIter.Syn.SynCat

open ProofRelevant.Semantics.Categorical (contextualLoop)
local notation "bindArrow" => ProofRelevant.Semantics.Categorical.bind

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

/-- Packing the native denotation of an application leaves the instruction as postcomposition. -/
theorem packedNative_op (pe : ε) {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {f : Φ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (instrSrc f)) :
    packedNative pe (.op (f := f) d) =
      packedNative pe d ≫ (instructionModel (τ := τ) pe).denote f :=
  (Category.assoc _ _ _).symm

/-- Packing the native denotation of a let gives binding on the packed context. -/
theorem packedNative_let1 (pe : ε) {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n}
    {s : Tm Empty Φ (n + 1)} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc β A) s B) :
    packedNative pe (.let₁ d e) =
      bindArrow (values (signature (τ := τ) (Φ := Φ) pe)) (packedNative pe d) (packedNative pe e) :=
  PackingProofs.packedNative_let1 pe d e

/-- Contextual binding in syntax pairs the original input with the scrutinee before continuing. -/
theorem bind_values {S : Sig.{u}} {X A B : ValueCat S}
    (f : X.obj ⟶ A.obj) (g : (X ⊗ A).obj ⟶ B.obj) :
    bindArrow (values S) f g = pairArrows (𝟙 X.obj) f ≫ g :=
  PackingProofs.bind_values f g

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ

/-- An arbitrary bound-variable lookup reifies to the packed context projection. -/
theorem packedNative_bv_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} (i : Fin n)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (.bv i) (β.get i)) :
    packedNative pe (Derivation.bv (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (ι := i) (β := β)) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h :=
  PackingProofs.packedNative_bv_eq_packedArrow pe i h

/-- The packed denotation of unit is the packed syntactic unit. -/
theorem packedNative_unit_eq_packedArrow (pe : ε) {n : Nat} {β : BoundCtx τ n}
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) .unit (Silmaril.unit : τ)) :
    packedNative pe (Derivation.unit (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (β := β)) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h :=
  PackingProofs.packedNative_unit_eq_packedArrow pe h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reification of an argument implies reification after applying a primitive. -/
theorem packedNative_op_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {f : Φ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (instrSrc f))
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) (instrSrc f))
    (ih : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h) :
    packedNative pe (.op (f := f) d) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (HasType.op (f := f) h) := by
  rw [packedNative_op pe d, ih, packedArrow_op h]
  rfl

/-- Reification of the scrutinee and body implies reification of their let. -/
theorem packedNative_let1_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 1)} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc β A) s B)
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (.snoc (Bridge.BoundCtx.toThesis β) A) (Bridge.toThesis s) B)
    (ih₁ : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ih₂ : packedNative pe e = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.let₁ d e) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.let₁ ha hb) :=
  PackingProofs.packedNative_let1_eq_packedArrow pe d e ha hb ih₁ ih₂

/-- Packing a left injection leaves the syntactic injection as postcomposition. -/
theorem packedNative_inl (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) :
    packedNative pe (Derivation.inl (B := B) d) =
      packedNative pe d ≫ injl (of (S := signature (τ := τ) (Φ := Φ) pe) A) (of B) :=
  PackingProofs.packedNative_inl pe d

/-- Reification of an argument implies reification of its left injection. -/
theorem packedNative_inl_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (ih : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h) :
    packedNative pe (Derivation.inl (B := B) d) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (HasType.inl (B := B) h) :=
  PackingProofs.packedNative_inl_eq_packedArrow pe d h ih

/-- Packing a right injection leaves the syntactic injection as postcomposition. -/
theorem packedNative_inr (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t B) :
    packedNative pe (Derivation.inr (A := A) d) =
      packedNative pe d ≫ injr (of (S := signature (τ := τ) (Φ := Φ) pe) A) (of B) :=
  PackingProofs.packedNative_inr pe d

/-- Reification of an argument implies reification of its right injection. -/
theorem packedNative_inr_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t B)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) B)
    (ih : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h) :
    packedNative pe (Derivation.inr (A := A) d) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (HasType.inr (A := A) h) :=
  PackingProofs.packedNative_inr_eq_packedArrow pe d h ih

/-- Packing a sequential pair evaluates each packed component in order. -/
theorem packedNative_pair (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t s : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) β s B) :
    packedNative pe (.pair d e) = pairArrows (packedNative pe d) (packedNative pe e) :=
  PackingProofs.packedNative_pair pe d e

/-- Reifying both components reifies their left-to-right sequential pair. -/
theorem packedNative_pair_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t s : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) β s B)
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis s) B)
    (ih₁ : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ih₂ : packedNative pe e = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.pair d e) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.pair ha hb) :=
  PackingProofs.packedNative_pair_eq_packedArrow pe d e ha hb ih₁ ih₂

/-- Product elimination retains the input, reassociates the pair, and runs the body. -/
theorem packedNative_let2 (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 2)} {A B C : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (product A B))
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc (.snoc β A) B) s C) :
    let S := signature (τ := τ) (Φ := Φ) pe
    let X := of (S := S) (packType (Bridge.BoundCtx.toThesis β))
    packedNative pe (.let₂ d e) =
      pairArrows (𝟙 X) (packedNative pe d) ≫ (tensorAssociator X (of A) (of B)).inv ≫
        packedNative pe e :=
  PackingProofs.packedNative_let2 pe d e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reifying a pair scrutinee and the two-slot body reifies their product elimination. -/
theorem packedNative_let2_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 2)} {A B C : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (product A B))
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc (.snoc β A) B) s C)
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) (product A B))
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (.snoc (.snoc (Bridge.BoundCtx.toThesis β) A) B) (Bridge.toThesis s) C)
    (ih₁ : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ih₂ : packedNative pe e = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.let₂ d e) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.let₂ ha hb) := by
  rw [packedNative_let2 pe d e, packedArrow_let2 ha hb, ih₁, ih₂]

/-- Packed case analysis retains the input and sends it into the selected branch. -/
theorem packedNative_case (pe : ε) {n : Nat} {β : BoundCtx τ n}
    {t : Tm Empty Φ n} {l r : Tm Empty Φ (n + 1)} {A B D : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (Silmaril.coprod A B))
    (dl : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc A) l D)
    (dr : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc B) r D) :
    let S := signature (τ := τ) (Φ := Φ) pe
    let X := of (S := S) (packType (Bridge.BoundCtx.toThesis β))
    packedNative pe (.case d dl dr) = pairArrows (𝟙 X) (packedNative pe d) ≫
      contextSumSplit X (of A) (of B) ≫ coprod.desc (packedNative pe dl) (packedNative pe dr) :=
  PackingProofs.packedNative_case pe d dl dr

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Reifying a scrutinee and both branches reifies their case expression. -/
theorem packedNative_case_eq_packedArrow (pe : ε) {n : Nat} {β : BoundCtx τ n}
    {t : Tm Empty Φ n} {l r : Tm Empty Φ (n + 1)} {A B D : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (Silmaril.coprod A B))
    (dl : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc A) l D)
    (dr : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc B) r D)
    (ht : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) (Silmaril.coprod A B))
    (hl : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (.snoc (Bridge.BoundCtx.toThesis β) A) (Bridge.toThesis l) D)
    (hr : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (.snoc (Bridge.BoundCtx.toThesis β) B) (Bridge.toThesis r) D)
    (iht : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ht)
    (ihl : packedNative pe dl = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hl)
    (ihr : packedNative pe dr = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hr) :
    packedNative pe (.case d dl dr) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.case ht hl hr) := by
  rw [packedNative_case pe d dl dr, packedArrow_case ht hl hr, iht, ihl, ihr]

/-- Pack the initial state and transport the native contextual loop to the packed input. -/
theorem packedNative_iter (pe : ε) {n : Nat} {β : BoundCtx τ n}
    {a : Tm Empty Φ n} {b : Tm Empty Φ (n + 1)} {A B : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc A) b (Silmaril.coprod B A)) :
    let S := signature (τ := τ) (Φ := Φ) pe
    let J := values S
    let X := of (S := S) (packType (Bridge.BoundCtx.toThesis β))
    packedNative pe (.iter da db) = pairArrows (𝟙 X) (packedNative pe da) ≫
      contextualLoop J (packedNative pe db ≫ J.map ((typeModel (Φ := Φ) pe).coprodIso B A).hom) :=
  PackingProofs.packedNative_iter pe da db

/-- On a packed syntax body, contextual iteration uses the whole packed state. -/
theorem contextualLoop_carried (pe : ε) {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {b : Thesis.LambdaIter.LocallyNameless.Tm Empty Φ (n + 1)}
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil ((Bridge.BoundCtx.toThesis β).snoc A) b (Silmaril.coprod B A)) :
    let J := values (signature (τ := τ) (Φ := Φ) pe)
    contextualLoop J (packedArrow hb ≫ J.map ((typeModel (Φ := Φ) pe).coprodIso B A).hom) =
      Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate (packedArrow (carriedIterTyping hb)) :=
  PackingProofs.contextualLoop_carried pe hb

/-- Reifying the initializer and the body reifies iteration with the original context. -/
theorem packedNative_iter_eq_packedArrow (pe : ε) {n : Nat} {β : BoundCtx τ n}
    {a : Tm Empty Φ n} {b : Tm Empty Φ (n + 1)} {A B : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc A) b (Silmaril.coprod B A))
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis a) A)
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil ((Bridge.BoundCtx.toThesis β).snoc A) (Bridge.toThesis b) (Silmaril.coprod B A))
    (iha : packedNative pe da = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ihb : packedNative pe db = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.iter da db) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.iter ha hb) :=
  PackingProofs.packedNative_iter_eq_packedArrow pe da db ha hb iha ihb

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
