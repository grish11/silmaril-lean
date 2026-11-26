module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Categorical.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Tests

open CategoryTheory CategoryTheory.Limits
open Silmaril.SSA.RVSDG.LambdaSSA
open LinearChain (localSite externalSite)
open LinearChain.Categorical (call choice)
open LambdaSSA.Semantics.Categorical
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w h k

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Y D E F : τ}

/-- The two paths from label 0 meet at local label 3. The final classifier
chooses distinct outward positions 0 and 1. -/
private abbrev diamond
    (test : TwoBlock.Instruction Φ A (coprod X Y))
    (left : TwoBlock.Instruction Φ X D) (right : TwoBlock.Instruction Φ Y D)
    (finish : TwoBlock.Instruction Φ D (coprod E F)) : Table Φ [E, F] 4 where
  types := ![A, X, Y, D]
  block := fun i =>
    let R := ![A, X, Y, D]
    let L := [E, F]
    Fin.cases (motive := fun j => Acyclic.Block Φ (List.ofFn R ++ L) (R j))
      (.branch test (localSite R L 1) (localSite R L 2))
      (fun j => Fin.cases
        (motive := fun j => Acyclic.Block Φ (List.ofFn R ++ L) (R j.succ))
        (.jump left (localSite R L 3))
        (fun j => Fin.cases
          (motive := fun j => Acyclic.Block Φ (List.ofFn R ++ L) (R j.succ.succ))
          (.jump right (localSite R L 3))
          (fun j => Fin.cases
            (motive := fun j => Acyclic.Block Φ (List.ofFn R ++ L) (R j.succ.succ.succ))
            (.branch finish (externalSite R L 0) (externalSite R L 1))
            (fun j => j.elim0) j) j) j) i

variable (test : TwoBlock.Instruction Φ A (coprod X Y))
  (left : TwoBlock.Instruction Φ X D) (right : TwoBlock.Instruction Φ Y D)
  (finish : TwoBlock.Instruction Φ D (coprod E F))

private theorem diamond_forward : (diamond test left right finish).Forward := by rfl

example :
    (List.finRange 4).map (fun i => ((diamond test left right finish).block i).targets) =
      [[1, 2], [3], [3], [4, 5]] := rfl

example (op : TwoBlock.Instruction Φ A A) :
    (Table.check (⟨fun _ => A, fun _ => .jump op (localSite (fun _ : Fin 1 => A) [E] 0)⟩ :
      Table Φ [E] 1)) = false := rfl

/-- Number the same diamond with the join first and the entry last. -/
private abbrev backwardDiamond : Table Φ [E, F] 4 where
  types := ![D, X, Y, A]
  block := fun i =>
    let R := ![D, X, Y, A]
    let L := [E, F]
    Fin.cases (motive := fun j => Acyclic.Block Φ (List.ofFn R ++ L) (R j))
      (.branch finish (externalSite R L 0) (externalSite R L 1))
      (fun j => Fin.cases
        (motive := fun j => Acyclic.Block Φ (List.ofFn R ++ L) (R j.succ))
        (.jump left (localSite R L 0))
        (fun j => Fin.cases
          (motive := fun j => Acyclic.Block Φ (List.ofFn R ++ L) (R j.succ.succ))
          (.jump right (localSite R L 0))
          (fun j => Fin.cases
            (motive := fun j => Acyclic.Block Φ (List.ofFn R ++ L) (R j.succ.succ.succ))
            (.branch test (localSite R L 1) (localSite R L 2))
            (fun j => j.elim0) j) j) j) i

example :
    (List.finRange 4).map (fun i => ((backwardDiamond test left right finish).block i).targets) =
      [[4, 5], [0], [0], [1, 2]] := rfl

example : (backwardDiamond test left right finish).check = false := rfl

private theorem backwardDiamond_acyclic :
    (backwardDiamond test left right finish).checkAcyclic = true := by cbv

example :
    let p := backwardDiamond test left right finish
    (List.finRange 4).map (p.acyclicRanking (backwardDiamond_acyclic test left right finish)).rank =
      [0, 1, 1, 2] := by cbv

/-- The chosen entry exits directly. Local blocks 1 and 2 form a genuine
two-edge cycle beyond that entry's reachable set. -/
private abbrev unreachableCycle (op : TwoBlock.Instruction Φ A A) : Table Φ [A] 3 where
  types := fun _ => A
  block i :=
    .jump op (if i = 0 then externalSite (fun _ : Fin 3 => A) [A] 0
      else localSite (fun _ : Fin 3 => A) [A] (if i = 1 then 2 else 1))

example (op : TwoBlock.Instruction Φ A A) : (unreachableCycle op).localTargets 0 = [] := rfl

example (op : TwoBlock.Instruction Φ A A) :
    Relation.TransGen (unreachableCycle op).LocalEdge 1 1 :=
  .tail (.single (show (unreachableCycle op).LocalEdge 1 2 from List.Mem.head _))
    (show (unreachableCycle op).LocalEdge 2 1 from List.Mem.head _)

example {d : Nat} {β : BoundCtx τ d} (op : TwoBlock.Instruction Φ A A) (a : Operand Φ β A) :
    (unreachableCycle op).toLetCase? 0 a = none := by
  have rejected : (unreachableCycle op).checkAcyclic = false := by cbv
  simp [Table.toLetCase?, rejected]

variable {d : Nat} {β : BoundCtx τ d}
variable (a : Operand Φ β A)

/-- This actual four-block region is outside the image of the structured
grammar, even though its denotation agrees with the structured lowering. -/
example (b : FiniteExit Φ [E, F] β) : (diamond test left right finish).toSSA 0 a ≠ b.toSSA := by
  cases b <;> simp [Table.toSSA, FiniteExit.toSSA, Region.linkExits]

variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

/-- Each path runs the entry operand, the first classifier, its selected
arm, and the shared classifier in that order. The last case preserves the
two distinct exit positions. No instruction interpretation is assumed central. -/
example :
    denoteRegion J M ((diamond test left right finish).toSSA_hasType 0 a) =
      denote J M (Morphism.CaseSSA.erase_hasType a.2.toHasType) ≫ choice J M test ≫
        coprod.desc (call J M left) (call J M right) ≫ choice J M finish ≫
        coprod.desc (J.map (labelInject M (L := [E, F]) 0 rfl))
          (J.map (labelInject M (L := [E, F]) 1 rfl)) := by
  let p := diamond test left right finish
  have h0 : p.resultAt J M 0 = choice J M test ≫
      coprod.desc (p.resultAt J M 1) (p.resultAt J M 2) := p.resultAt_step J M 0
  have h1 : p.resultAt J M 1 = call J M left ≫ p.resultAt J M 3 := p.resultAt_step J M 1
  have h2 : p.resultAt J M 2 = call J M right ≫ p.resultAt J M 3 := p.resultAt_step J M 2
  have h3 : p.resultAt J M 3 = choice J M finish ≫
      coprod.desc (J.map (labelInject M (L := [E, F]) 0 rfl))
        (J.map (labelInject M (L := [E, F]) 1 rfl)) := p.resultAt_step J M 3
  calc
    _ = denote J M (Morphism.CaseSSA.erase_hasType a.2.toHasType) ≫ p.resultAt J M 0 :=
      p.toSSA_denote J M 0 a
    _ = _ := by
      simp only [h0, h1, h2, h3, coprod.desc_comp]

example : let p := diamond test left right finish
    denoteRegion J M (p.toFiniteExit (diamond_forward test left right finish) 0 a).toSSA_hasType =
      denoteRegion J M (p.toSSA_hasType 0 a) :=
  (diamond test left right finish).toFiniteExit_denote J M (diamond_forward test left right finish) 0 a

/-- The executable admission uses the unchanged native table and entry index. -/
example :
    let p := backwardDiamond test left right finish
    (p.toLetCase? 3 a).isSome = true :=
  ((backwardDiamond test left right finish).toLetCase?_isSome 3 a).trans
    (backwardDiamond_acyclic test left right finish)

example :
    denoteRegion J M ((backwardDiamond test left right finish).toSSA_hasType 3 a) =
      denote J M (Morphism.CaseSSA.erase_hasType a.2.toHasType) ≫ choice J M test ≫
        coprod.desc (call J M left) (call J M right) ≫ choice J M finish ≫
        coprod.desc (J.map (labelInject M (L := [E, F]) 0 rfl))
          (J.map (labelInject M (L := [E, F]) 1 rfl)) := by
  let p := backwardDiamond test left right finish
  have h3 : p.resultAt J M 3 = choice J M test ≫
      coprod.desc (p.resultAt J M 1) (p.resultAt J M 2) := p.resultAt_step J M 3
  have h1 : p.resultAt J M 1 = call J M left ≫ p.resultAt J M 0 := p.resultAt_step J M 1
  have h2 : p.resultAt J M 2 = call J M right ≫ p.resultAt J M 0 := p.resultAt_step J M 2
  have h0 : p.resultAt J M 0 = choice J M finish ≫
      coprod.desc (J.map (labelInject M (L := [E, F]) 0 rfl))
        (J.map (labelInject M (L := [E, F]) 1 rfl)) := p.resultAt_step J M 0
  calc
    _ = denote J M (Morphism.CaseSSA.erase_hasType a.2.toHasType) ≫ p.resultAt J M 3 :=
      p.toSSA_denote J M 3 a
    _ = _ := by simp only [h3, h1, h2, h0, coprod.desc_comp]

example :
    let p := backwardDiamond test left right finish
    let r := p.acyclicRanking (backwardDiamond_acyclic test left right finish)
    denoteRegion J M (p.toFiniteExitRanked r 3 a).toSSA_hasType =
      denoteRegion J M (p.toSSA_hasType 3 a) :=
  (backwardDiamond test left right finish).toFiniteExitRanked_denote J M
    ((backwardDiamond test left right finish).acyclicRanking (backwardDiamond_acyclic test left right finish)) 3 a

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Tests
