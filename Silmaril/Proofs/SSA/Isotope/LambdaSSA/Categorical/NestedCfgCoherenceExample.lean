module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.BlockParameters.Thms

/-! # An inner native loop dispatching to an outer block or exit -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgFixture

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open UnusedSummand.BlockParameters
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

private inductive Op where
  | load
  | inspect

private abbrev U : Ty Empty := Silmaril.unit
private abbrev Flag : Ty Empty := Silmaril.coprod U U
private abbrev Reply : Ty Empty := Silmaril.coprod U Flag
private abbrev Result : Ty Empty := Silmaril.product U Flag
private abbrev exits : LCtx (Ty Empty) := [U, Result]

instance : HasTy Op (Ty Empty) where
  src
    | .load => U
    | .inspect => Flag
  trg
    | .load => Flag
    | .inspect => Reply

instance : HasEff Op Bool := ⟨fun _ => true⟩

private def outerFamily : Fin 2 → Ty Empty := Fin.cases Flag (fun _ => Result)
private def innerFamily (dead : Ty Empty) : Fin 2 → Ty Empty := Fin.cases Flag (fun _ => dead)

private abbrev outerLabels := List.ofFn outerFamily ++ exits

private def inner : Program (Φ := Op) (innerFamily U) outerLabels [Flag, U] where
  entry := .jump 0 (.var 0 rfl)
  blocks := Fin.cases
    (.parameter (.case (.op Op.inspect (.var 0 rfl))
      (.jump 0 (.var 1 rfl))
      (.case (.var 0 rfl)
        (.exit 1 rfl (.pair (.var 4 rfl) (.var 3 rfl)))
        (.exit 2 rfl (.var 0 rfl)))))
    (fun _ => .captured (.exit 2 rfl .unit))

private def innerEntry : Region Op := .br 0 (.var 0)

private def innerRows : Fin 2 → Region Op := Fin.cases
  (.case (.op Op.inspect (.var 0)) (.br 0 (.var 1))
    (.case (.var 0) (.br 3 (.pair (.var 4) (.var 3))) (.br 4 (.var 0))))
  (fun _ => .br 4 .unit)

private abbrev innerRegion : Region Op := .cfg innerEntry 2 innerRows

private theorem inner_written : inner.region = innerRegion := by
  change inner.region = .cfg innerEntry 2 innerRows
  unfold Program.region inner innerRows
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem inner_reaches : inner.Reaches 0 := .entry rfl

private theorem inner_targets {i : Fin 2} (hit : inner.targets i) : i = 0 := by
  rcases hit with hit | ⟨j, hit⟩
  · exact (show (0 : Fin 2) = i from hit).symm
  · revert hit
    refine Fin.cases ?_ (fun _ h => h.elim) j
    rintro (h | h)
    · exact (show (0 : Fin 2) = i from h).symm
    · rcases h with h | h <;> exact h.elim

private theorem closed : inner.ReachableParameters where
  targets _ hit := inner_targets hit ▸ inner_reaches
  parameters i := Fin.cases (fun _ => inner_reaches) (fun _ h => h.elim) i

private theorem innerEntry_typed (D : Ty Empty) :
    innerEntry.HasType [Flag, U] (List.ofFn (innerFamily D) ++ outerLabels) :=
  .br rfl (.var rfl)

private theorem innerRows_typed (D : Ty Empty) (i : Fin 2) :
    (innerRows i).HasType (innerFamily D i :: [Flag, U]) (List.ofFn (innerFamily D) ++ outerLabels) :=
  Fin.cases (.case (.op (.var rfl)) (.br rfl (.var rfl))
    (.case (.var rfl) (.br rfl (.pair (.var rfl) (.var rfl))) (.br rfl (.var rfl))))
    (fun _ => .br rfl .unit) i

private def outerEntry : Region Op := .br 0 (.op Op.load (.var 0))
private def outerRows : Fin 2 → Region Op := Fin.cases innerRegion (fun _ => .br 3 (.var 0))
private abbrev outerRegion : Region Op := .cfg outerEntry 2 outerRows

private theorem outerEntry_typed : outerEntry.HasType [U] outerLabels := .br rfl (.op (.var rfl))

private theorem outerRows_typed (D : Ty Empty) (i : Fin 2) :
    (outerRows i).HasType (outerFamily i :: [U]) outerLabels :=
  Fin.cases (.cfg (innerFamily D) (innerEntry_typed D) (innerRows_typed D)) (fun _ => .br rfl (.var rfl)) i

private theorem outerFamily_determined : LabelsDetermined [U] exits outerEntry outerRows outerFamily := by
  intro S he hb
  have first : S 0 = Flag := by
    cases he with
    | br target arg =>
        have label : At (List.ofFn S ++ exits) 0 (S 0) := by simp [At]
        cases arg
        exact Option.some.inj (label.symm.trans target)
  have second : S 1 = Result :=
    outward_parameter_type (L := exits) (S := S) (i := 1) (j := 1) (show At exits 1 Result from rfl) (hb 1)
  funext i
  refine Fin.cases first (Fin.cases second ?_) i
  intro j
  exact Fin.elim0 j

private theorem innerDead_differs : innerFamily U 1 ≠ innerFamily .empty 1 := by
  intro eq
  cases eq

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

private theorem outer_functional (roll : IterationRolling C) :
    RegionDenotes.Functional J M [U] outerRegion exits := by
  apply RegionDenotes.Functional.cfg J M outerFamily_determined
  · exact (DeterminedRegion.br rfl (.op (.var rfl))).functional J M
  · intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · change RegionDenotes.Functional J M [Flag, U] innerRegion outerLabels
      rw [← inner_written]
      exact fun {_ _ _ _} d e => inner.denotes_eq J M roll closed d e
    · exact (DeterminedRegion.br rfl (.var rfl)).functional J M

local notation "Arrow" => J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M exits)

private def NestedAt (dead : Ty Empty) (f : Arrow) : Prop :=
  ∃ (entry : J.obj (ctxObj M [U]) ⟶ J.obj (labelObj M outerLabels))
    (rows : ∀ i, J.obj (ctxObj M (outerFamily i :: [U])) ⟶ J.obj (labelObj M outerLabels))
    (dispatch : J.obj (ctxObj M [U] ⊗ finiteLabelObj M outerFamily) ⟶ J.obj (labelObj M outerLabels)),
    RegionDenotes J M outerEntry_typed entry ∧
      CfgDenotesAt J M (innerFamily dead) innerEntry innerRows (rows 0) ∧
      RegionDenotes J M (outerRows_typed dead 1) (rows 1) ∧
      CollectiveDenotes J M [U] outerFamily exits rows dispatch ∧
      f = cfgDispatchArrow J M outerFamily entry dispatch

private theorem nested_exists (D : Ty Empty) : ∃ f : Arrow, NestedAt J M D f := by
  obtain ⟨innerArrow, exactInner⟩ := CfgDenotesAt.exists_of_typing J M (innerFamily D)
    (innerEntry_typed D) (innerRows_typed D)
  let rows (i : Fin 2) : J.obj (ctxObj M (outerFamily i :: [U])) ⟶ J.obj (labelObj M outerLabels) :=
    Fin.cases innerArrow (fun _ => denoteRegion J M (outerRows_typed D 1)) i
  obtain ⟨dispatch, blocks⟩ := collective_exists J M 1 [U] outerFamily (labelObj M outerLabels) rows
  exact ⟨_, _, rows, dispatch, denoteRegion_spec J M outerEntry_typed, exactInner,
    denoteRegion_spec J M (outerRows_typed D 1), ⟨blocks⟩, rfl⟩

private theorem NestedAt.denotes {D : Ty Empty} {f : Arrow} (w : NestedAt J M D f) :
    RegionDenotes J M (.cfg outerFamily outerEntry_typed (outerRows_typed D)) f := by
  obtain ⟨entry, rows, dispatch, de, di, dr, dc, eq⟩ := w
  apply CfgDenotesAt.denotes J M (R := outerFamily)
  refine ⟨outerEntry_typed, outerRows_typed D, entry, rows, dispatch, de, ?_, dc, eq⟩
  intro i
  refine Fin.cases (di.denotes J M) (Fin.cases dr ?_) i
  intro j
  exact Fin.elim0 j

/-- The inner repeat stays native. An inspect reply can also transfer to
outer block 1 with both captures or exit directly at outward label 0.
Outer block 1 sends its pair to outward label 1. Two independently assembled
top-level witnesses use different types at the dead inner slot. -/
example (roll : IterationRolling C) :
    innerFamily U 1 ≠ innerFamily .empty 1 ∧
      ∃ f g : Arrow, NestedAt J M U f ∧ NestedAt J M .empty g ∧ f = g := by
  obtain ⟨f, left⟩ := nested_exists J M U
  obtain ⟨g, right⟩ := nested_exists J M .empty
  exact ⟨innerDead_differs, f, g, left, right,
    outer_functional J M roll (left.denotes J M) (right.denotes J M)⟩

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgFixture
