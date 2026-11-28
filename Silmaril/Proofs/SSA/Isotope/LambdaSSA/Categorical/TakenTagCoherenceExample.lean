module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.TakenTag.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms

/-! # A forwarding cycle with two exact live typings and ordered exits -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.TakenTagFixture

open CategoryTheory CategoryTheory.Limits
open UnusedSummand
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

private inductive Op where
  | route

private abbrev U : Ty Empty := Silmaril.unit
private abbrev Reply : Ty Empty := Silmaril.coprod U (Silmaril.coprod U U)
private abbrev Pair : Ty Empty := Silmaril.product U U
private abbrev exits : LCtx (Ty Empty) := [U, Pair]

instance : HasTy Op (Ty Empty) := ⟨fun _ => U, fun _ => Reply⟩
instance : HasEff Op Bool := ⟨fun _ => true⟩

private def payload : Fin 2 → Ty Empty := fun _ => U

private def wideEntry : Region Op := .br 0 (.inl .unit)

private def wideRows : Fin 2 → Region Op :=
  Fin.cases (.br 1 (.var 0)) (fun _ =>
    .case (.var 0)
      (.case (.op Op.route (.var 0))
        (.br 0 (.var 2))
        (.case (.var 0) (.br 2 (.var 0)) (.br 3 (.pair (.var 0) (.var 2)))))
      (.br 0 (.var 1)))

private abbrev cycle : Region Op := .cfg wideEntry 2 wideRows

private def commonEntry : Row (Φ := Op) payload exits [] := .jump 0 .unit

private def commonRows (i : Fin 2) : Row (Φ := Op) payload exits [payload i] :=
  Fin.cases (.jump 1 (.var 0 rfl)) (fun _ =>
    .case (.op Op.route (.var 0 rfl))
      (.jump 0 (.var 1 rfl))
      (.case (.var 0 rfl) (.exit 0 rfl (.var 0 rfl))
        (.exit 1 rfl (.pair (.var 0 rfl) (.var 2 rfl))))) i

private theorem prune (i : Fin 2) : Region.PruneConstructorTests
    ((wideRows i).substVars (Tm.replaceNewest (.inl (.var 0)))) ((commonRows i).region true id) := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · exact .keep _
  · exact .inl (.keep _)

private theorem wideEntry_typed (D : Ty Empty) :
    wideEntry.HasType [] (List.ofFn (family payload (some (fun _ => D))) ++ exits) :=
  .br rfl (.inl .unit)

private theorem wideRows_typed (D : Ty Empty) (i : Fin 2) :
    (wideRows i).HasType [family payload (some (fun _ => D)) i]
      (List.ofFn (family payload (some (fun _ => D))) ++ exits) :=
  Fin.cases (.br rfl (.var rfl)) (fun _ =>
    .case (.var rfl) (.case (.op (.var rfl)) (.br rfl (.var rfl))
      (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.pair (.var rfl) (.var rfl)))))
      (.br rfl (.var rfl))) i

private theorem selected_family {S : Fin 2 → Ty Empty}
    (entry : wideEntry.HasType [] (List.ofFn S ++ exits))
    (rows : ∀ i, (wideRows i).HasType [S i] (List.ofFn S ++ exits)) :
    ∃ D : Ty Empty, S = family payload (some (fun _ => D)) := by
  have first : ∃ D : Ty Empty, S 0 = Silmaril.coprod U D := by
    cases entry with
    | br target typed =>
        have label : At (List.ofFn S ++ exits) 0 (S 0) := by simp [At]
        have eq := Option.some.inj (label.symm.trans target)
        cases typed with
        | inl value =>
            cases value
            exact ⟨_, eq⟩
  have second : S 1 = S 0 := by
    have row := rows 0
    change (Region.br 1 (.var 0) : Region Op).HasType [S 0] (List.ofFn S ++ exits) at row
    cases row with
    | br target arg =>
        cases arg with
        | var hit =>
            have label : At (List.ofFn S ++ exits) 1 (S 1) := by simp [At]
            exact (Option.some.inj (label.symm.trans target)).trans (Option.some.inj hit).symm
  obtain ⟨D, head⟩ := first
  refine ⟨D, funext (Fin.cases head (Fin.cases (second.trans head) ?_))⟩
  intro i
  exact Fin.elim0 i

/-- Both reached slots really have different types in the two graphs. -/
example (i : Fin 2) :
    family payload (some (fun _ => U)) i ≠ family payload (some (fun _ => .empty)) i := by
  intro eq
  have impossible := (Ty.coprod.inj eq).2
  cases impossible

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

/-- Both exact graphs exist independently. The same two live slots
are typed by Unit + Unit in one and Unit + Empty in the other. -/
example :
    (∃ f : Arrow, CfgDenotesAt J M (family payload (some (fun _ => U))) wideEntry wideRows f) ∧
    (∃ g : Arrow, CfgDenotesAt J M (family payload (some (fun _ => .empty))) wideEntry wideRows g) :=
  ⟨CfgDenotesAt.exists_of_typing J M _ (wideEntry_typed U) (wideRows_typed U),
   CfgDenotesAt.exists_of_typing J M _ (wideEntry_typed .empty) (wideRows_typed .empty)⟩

private theorem compare_with_common (f g : Arrow)
    (common : CfgDenotesAt J M payload (commonEntry.region false id)
      (fun i => (commonRows i).region false id) f)
    {t : cycle.HasType [] exits} (wide : RegionDenotes J M t g) : f = g := by
  obtain ⟨S, readback⟩ := wide.cfg_readback J M
  have shape : ∃ D : Ty Empty, S = family payload (some (fun _ => D)) := by
    obtain ⟨entry, rows, _⟩ := readback
    exact selected_family entry rows
  obtain ⟨D, rfl⟩ := shape
  exact CfgDenotesAt.eq_of_taken_tag J M (fun _ => D) commonEntry commonRows
    wideRows prune common readback

/-- Arbitrary exact witnesses of the written cycle agree. Each round
forwards the live argument, tests its known tag, and runs the route
instruction once. The reply can repeat or take either ordered exit. -/
example {t t' : cycle.HasType [] exits} {f g : Arrow}
    (left : RegionDenotes J M t f) (right : RegionDenotes J M t' g) : f = g := by
  obtain ⟨common, d⟩ := CfgDenotesAt.exists_of_typing J M payload
    (commonEntry.hasType (Ren.id _) none) (fun i => (commonRows i).hasType (Ren.id _) none)
  exact (compare_with_common J M common f d left).symm.trans (compare_with_common J M common g d right)

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.TakenTagFixture
