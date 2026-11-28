module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms
public import Silmaril.Semantics.Calco2019.Maybe.Types.Thms

/-! # A cyclic square whose written target requires a binary entry move -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.WithEntryLet (Site ofRegion_comp_constructor)
open Paper.WithEntryLet.OperandExample (X D Bit taggedSource_forget)
open Paper.WithBoundEntryEta (move₂ moveEntry₂ move₂_substVars repairTarget uniformity_of_target_move₂)
open Paper.WithBoundEntryEta.ReplayExample Paper.EntryLetObstruction.Destructure
open Paper.Extension.Singleton (projection projectStep iterateChosen projectSquare_iff)
open SequencingObstruction (Instruction)

local notation "Proj" => projection Seed
local notation "Unary" => Paper.WithEntryLet.Step (τ := Ty Empty) (Φ := Instruction)

set_option backward.isDefEq.respectTransparency false

theorem movedTarget_eq :
    ofRegion movedStep_typed ≫ (sumIso U U).hom =
      ofRegion moved_typed ≫ discardArrow U ≫ coprod.inr := by
  let h : ValueBranches [U] (.br 0 (.inr .unit) : Region Instruction) [Bit] :=
    .br rfl (.inr .unit)
  have leg : discardArrow (Φ := Instruction) U ≫ (sumCofan U U).inr = ofRegion h := by
    rw [sumCofan_inr]
    rfl
  rw [← ofRegion_comp moved_typed h movedStep_typed, ← leg]
  simp

private theorem repaired_square :
    source ≫ coprod.map (𝟙 X) forget = forget ≫ ofRegion movedStep_typed ≫ (sumIso U U).hom := by
  rw [movedTarget_eq]
  exact taggedSource_forget _

private theorem move_written :
    move₂ .here (recurring original) = some (recurring moved) := by
  simp only [move₂, Site.rewriteAt, moveEntry₂, recurring, original, moved, entry, compLSubst, lsubst]
  congr 2
  apply congrArg (Region.cfg (.br 0 (.var 1) : Region Instruction) 2)
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => j.elim0)) i

private abbrev substForget : Nat → Tm Instruction := Tm.singleSubst .unit ∘ lift Nat.succ

private theorem substForget_typed :
    ∀ ⦃i A⦄, At [U] i A → Tm.BranchValue [Bit] (substForget i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .unit
  | succ i => simp [At] at hi

private theorem movedComposite :
    ValueBranches [Bit] ((recurring moved).substVars substForget) [Bit] :=
  movedStep_typed.substVars substForget_typed

private theorem move_composite :
    move₂ .here ((recurring original).substVars substForget) = some ((recurring moved).substVars substForget) := by
  rw [move₂_substVars, move_written]
  rfl

private theorem native_composite :
    source ≫ coprod.map (𝟙 X) forget = ofRegion movedComposite ≫ (sumIso U U).hom := by
  have ex : forget ≫ ofRegion movedStep_typed = ofRegion movedComposite :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) movedStep_typed movedComposite
  rw [repaired_square, ← Category.assoc forget, ex]

private theorem flatComposite :
    ValueBranches [Bit] ((recurring original).substVars substForget) [Bit] :=
  flatStep_typed.substVars substForget_typed

theorem unary_square_ne :
    projectStep Unary source ≫ coprod.map (𝟙 ((projection Unary).obj X)) ((projection Unary).map forget) ≠
      (projection Unary).map forget ≫ projectStep Unary target := by
  have expose : forget ≫ ofRegion flatStep_typed = ofRegion flatComposite :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) flatStep_typed flatComposite
  intro square
  have equal := (projectSquare_iff Unary source target forget).1 square
  rw [native_composite, target, ← Category.assoc forget, expose, Functor.map_comp, Functor.map_comp] at equal
  exact recurring_ne ((Paper.Extension.Singleton.ofRegion_eq_iff Unary movedComposite flatComposite).1
    ((cancel_mono ((projection Unary).map ((sumIso U U).hom))).1 equal))

theorem native_square_ne :
    source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ target :=
  fun eq => unary_square_ne ((projectSquare_iff Unary source target forget).2 (congrArg _ eq))

theorem repaired :
    ∃ g : X ⟶ X ⨿ X, projectStep Seed g = projectStep Seed target ∧
      source ≫ coprod.map (𝟙 X) forget = forget ≫ g :=
  repairTarget .here (.unit (Γ := [Bit])) flatStep_typed source movedComposite move_composite native_composite

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((Proj).obj X)) ((Proj).map forget) =
      (Proj).map forget ≫ projectStep Seed target := by
  obtain ⟨g, hg, native⟩ := repaired
  rw [← hg]
  exact (projectSquare_iff Seed source g forget).2 (congrArg ((Proj).map) native)

theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (Proj).map forget ≫ iterateChosen Seed (projectStep Seed target) :=
  uniformity_of_target_move₂ .here (.unit (Γ := [Bit])) flatStep_typed source
    movedComposite move_composite native_composite

private theorem left_forget : (sumCofan (Φ := Instruction) U U).inl ≫ forget = discardArrow U := by
  rw [sumCofan_inl]
  exact discard_comp_branchValue (.inl (.var rfl))

private theorem right_forget : (sumCofan (Φ := Instruction) U U).inr ≫ forget = discardArrow U := by
  rw [sumCofan_inr]
  exact discard_comp_branchValue (.inr (.var rfl))

section DistinctTags

open scoped MonoidalCategory
open Semantics.Interaction.Typed (AtomValues typeModel)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

local instance : AtomValues Empty where
  carrier a := a.elim

attribute [local instance] typeModel

local instance : HasEff Instruction Bool where
  eff _ := false

local notation "Maybe" => Silmaril.Calco2019.Maybe.Types.Model
local notation "M" => ofMonadicTypeModel (τ := Ty Empty)
local notation "K" => typeJ (m := Maybe)

local instance : InstructionModel Instruction (Ty Empty) Bool Maybe where
  denote _ x := pure x
  denotePure _ _ x := x
  denote_pure _ _ _ := rfl

local instance : Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel K M Instruction :=
  ofMonadicInstructionModel (ε := Bool)

private theorem projected_tags_ne :
    (Proj).map (sumCofan (Φ := Instruction) U U).inl ≠ (Proj).map (sumCofan U U).inr := by
  let : RegionTypingCoherent (Φ := Instruction) K M :=
    Semantics.Erasure.regionTypingCoherent (κ := Empty) (Φ := Instruction) (m := Maybe)
      (fun _ x => pure x) (.inr .unit) (.inr .unit)
      (fun f x => by cases f; cases x; rfl)
  intro eq
  let shared : ∀ A B : Type, ∃ h : (K).obj A ⊗ (K).obj B = (K).obj (A ⊗ B),
      Functor.StrongPremonoidal.tensorIso (J := K) A B = eqToIso h :=
    fun _ _ => ⟨rfl, rfl⟩
  let F := Paper.Extension.Singleton.denoteFunctor (Seed := Seed) K M shared
    (Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.seedDenotes K M shared)
  have e := congrArg (fun k => F.map k) eq
  dsimp only [F] at e
  rw [sumCofan_inl, sumCofan_inr, Paper.Extension.Singleton.denoteFunctor_map_ofRegion,
    Paper.Extension.Singleton.denoteFunctor_map_ofRegion,
    denoteSingletonRegion_br K M (.inl (.var (i := 0) rfl)),
    denoteSingletonRegion_br K M (.inr (.var (i := 0) rfl))] at e
  simp only [lookup, ← Functor.map_comp] at e
  change (K).map (coprod.inl ≫ (Types.binaryCoproductIso PUnit PUnit).hom) =
    (K).map (coprod.inr ≫ (Types.binaryCoproductIso PUnit PUnit).hom) at e
  rw [Types.binaryCoproductIso_inl_comp_hom, Types.binaryCoproductIso_inr_comp_hom] at e
  have out := congrArg (fun k => k.of PUnit.unit) e
  change Sum.inl (Sum.inl PUnit.unit) = Sum.inl (Sum.inr PUnit.unit) at out
  have tags : (Sum.inl PUnit.unit : PUnit ⊕ PUnit) = .inr PUnit.unit := Sum.inl.inj out
  cases tags

theorem no_retraction : ¬ ∃ k : (Proj).obj X ⟶ (Proj).obj D, (Proj).map forget ≫ k = 𝟙 ((Proj).obj D) := by
  rintro ⟨k, hk⟩
  let i : X ⟶ D := (sumCofan U U).inl
  let j : X ⟶ D := (sumCofan U U).inr
  have eq : (Proj).map i = (Proj).map j := by
    calc
      _ = ((Proj).map i ≫ (Proj).map forget) ≫ k := by rw [Category.assoc, hk, Category.comp_id]
      _ = ((Proj).map j ≫ (Proj).map forget) ≫ k := by
        rw [← Functor.map_comp, ← Functor.map_comp, left_forget, right_forget]
      _ = _ := by rw [Category.assoc, hk, Category.comp_id]
  exact projected_tags_ne eq

end DistinctTags


end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample
