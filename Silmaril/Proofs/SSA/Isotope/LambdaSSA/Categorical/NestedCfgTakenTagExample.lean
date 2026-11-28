module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-! # Both native iterations survive a change of a live outer sum type -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedTakenTagFixture

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private inductive Op where
  | route

private abbrev U : Ty Empty := Silmaril.unit
private abbrev Pair : Ty Empty := Silmaril.product U U
private abbrev Reply : Ty Empty := Silmaril.coprod U (Silmaril.coprod U (Silmaril.coprod U U))
private abbrev exits : LCtx (Ty Empty) := [U, Pair]
private abbrev tagged (D : Ty Empty) := Silmaril.coprod U D
private abbrev slots (A : Ty Empty) : Fin 1 → Ty Empty := fun _ => A
private abbrev labels (A : Ty Empty) : LCtx (Ty Empty) := List.ofFn (slots A) ++ exits

instance : HasTy Op (Ty Empty) := ⟨fun _ => U, fun _ => Reply⟩
instance : HasEff Op Bool := ⟨fun _ => true⟩

private def wideEntry : Region Op := .br 0 (.inl .unit)

private def tagPayload (tag : Bool) (a : Tm Op) : Tm Op := if tag then .inl a else a

private def guarded (body : Region Op) : Region Op :=
  .case (.var 0) (body.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 0 (.var 1))

private theorem guard_typed {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {D : Ty Empty}
    {body : Region Op} (h : body.HasType (U :: Γ) L) (target : At L 0 (tagged D)) :
    (guarded body).HasType (tagged D :: Γ) L :=
  .case (.var rfl) (h.renameVars ((Ren.wk Γ (tagged D)).lift U)) (.br target (.var rfl))

private def innerEntry (loopTag : Bool) : Region Op := .br 0 (tagPayload loopTag (.var 0))

private def round (again transfer first second : Region Op) : Region Op :=
  .case (.op Op.route (.var 0)) again (.case (.var 0) transfer (.case (.var 0) first second))

private def innerStep (outerTag loopTag : Bool) : Region Op :=
  round (.br 0 (tagPayload loopTag (.var 1))) (.br 1 (tagPayload outerTag (.var 2)))
    (.br 2 (.var 0)) (.br 3 (.pair (.var 0) (.var 4)))

private def innerRow (outerTag loopTag : Bool) : Region Op :=
  if loopTag then guarded (innerStep outerTag true) else innerStep outerTag false

private def keep : Fin 1 ↪ Fin 2 := ⟨fun _ => 0, by intro a b _; exact Subsingleton.elim a b⟩
private def innerStates (live dead : Ty Empty) : Fin 2 → Ty Empty := Fin.cases live (fun _ => dead)
private def innerRows (outerTag loopTag : Bool) : Fin 2 → Region Op :=
  Fin.cases (innerRow outerTag loopTag) (fun _ => .br 2 .unit)

private abbrev actualInnerEntry (loopTag : Bool) :=
  (innerEntry loopTag).renameLabels (retainLabelIndex keep)
private abbrev actualInnerRows (outerTag loopTag : Bool) (i : Fin 2) :=
  (innerRows outerTag loopTag i).renameLabels (retainLabelIndex keep)
private abbrev inner (outerTag loopTag : Bool) : Region Op :=
  .cfg (actualInnerEntry loopTag) 2 (actualInnerRows outerTag loopTag)

private abbrev wideRow (loopTag : Bool) : Region Op := guarded (inner true loopTag)
private abbrev original (loopTag : Bool) : Region Op := .cfg wideEntry 1 (fun _ => wideRow loopTag)

private abbrev innerType (loopTag : Bool) (D : Ty Empty) := if loopTag then tagged D else U

private theorem innerEntry_typed (Γ : VCtx (Ty Empty)) (A : Ty Empty) (loopTag : Bool) (D : Ty Empty) :
    (innerEntry loopTag).HasType (U :: Γ) (List.ofFn (slots (innerType loopTag D)) ++ labels A) := by
  cases loopTag
  · exact .br rfl (.var rfl)
  · exact .br rfl (.inl (.var rfl))

private theorem innerStep_typed (Γ : VCtx (Ty Empty)) (outerTag loopTag : Bool) (D E : Ty Empty) :
    (innerStep outerTag loopTag).HasType (U :: U :: Γ)
      (List.ofFn (slots (innerType loopTag E)) ++ labels (innerType outerTag D)) := by
  refine .case (.op (.var rfl)) ?_ (.case (.var rfl) ?_
    (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.pair (.var rfl) (.var rfl)))))
  · cases loopTag
    · exact .br rfl (.var rfl)
    · exact .br rfl (.inl (.var rfl))
  · cases outerTag
    · exact .br rfl (.var rfl)
    · exact .br rfl (.inl (.var rfl))

private theorem exactInnerEntry (Γ : VCtx (Ty Empty)) (A : Ty Empty) (loopTag : Bool) (D dead : Ty Empty) :
    (actualInnerEntry loopTag).HasType (U :: Γ)
      (List.ofFn (innerStates (innerType loopTag D) dead) ++ labels A) :=
  (innerEntry_typed Γ A loopTag D).renameLabels (retainLabelRen keep _ _)

private theorem exactInnerRows (Γ : VCtx (Ty Empty)) (outerTag loopTag : Bool) (D E dead : Ty Empty)
    (i : Fin 2) : (actualInnerRows outerTag loopTag i).HasType
      (innerStates (innerType loopTag E) dead i :: U :: Γ)
      (List.ofFn (innerStates (innerType loopTag E) dead) ++ labels (innerType outerTag D)) := by
  have ren := retainLabelRen keep (innerStates (innerType loopTag E) dead) (labels (innerType outerTag D))
  refine Fin.cases ?_ (fun _ => ?_) i
  · cases loopTag
    · exact (innerStep_typed Γ outerTag false D E).renameLabels ren
    · exact (guard_typed (innerStep_typed Γ outerTag true D E) rfl).renameLabels ren
  · have h : (Region.br 2 .unit : Region Op).HasType (dead :: U :: Γ)
        (List.ofFn (slots (innerType loopTag E)) ++ labels (innerType outerTag D)) := .br rfl .unit
    exact h.renameLabels ren

private theorem inner_typed (Γ : VCtx (Ty Empty)) (outerTag loopTag : Bool) (D E dead : Ty Empty) :
    (inner outerTag loopTag).HasType (U :: Γ) (labels (innerType outerTag D)) :=
  .cfg (innerStates (innerType loopTag E) dead)
    (exactInnerEntry Γ (innerType outerTag D) loopTag E dead)
    (exactInnerRows Γ outerTag loopTag D E dead)

private theorem wideRow_typed (loopTag : Bool) (D E dead : Ty Empty) :
    (wideRow loopTag).HasType [tagged D] (labels (tagged D)) :=
  guard_typed (inner_typed [] true loopTag D E dead) rfl

private def rejectedRound (removed : Bool) : Region Op :=
  round (if removed then .br 1 .unit else .br 0 (.var 1))
    (.br 2 (if removed then .inl (.var 2) else .inr .unit))
    (.br 3 (.var 0)) (.br 4 (.pair (.var 0) (.var 4)))

private def rejectedRows (removed : Bool) : Fin 2 → Region Op :=
  Fin.cases (rejectedRound removed) (fun _ => .br 3 .unit)

private abbrev rejectedInner (removed : Bool) : Region Op :=
  .cfg (.br 0 (.var 0)) 2 (rejectedRows removed)

private abbrev rejected (removed : Bool) : Region Op :=
  .cfg wideEntry 1 (fun _ => guarded (rejectedInner removed))

private theorem rejected_typed (removed : Bool) : (rejected removed).HasType [] exits := by
  refine .cfg (slots (tagged U)) (.br rfl (.inl .unit)) (fun _ => guard_typed ?_ rfl)
  refine .cfg (innerStates U U) (.br rfl (.var rfl)) (fun i => Fin.cases ?_ (fun _ => .br rfl .unit) i)
  cases removed
  · exact .case (.op (.var rfl)) (.br rfl (.var rfl))
      (.case (.var rfl) (.br rfl (.inr .unit))
        (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.pair (.var rfl) (.var rfl)))))
  · exact .case (.op (.var rfl)) (.br rfl .unit)
      (.case (.var rfl) (.br rfl (.inl (.var rfl)))
        (.case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.pair (.var rfl) (.var rfl)))))

/-- Both graphs are exactly typed. The checker gives unknown on a right
payload at the outer transfer and on a transfer into the removed slot. -/
example (removed : Bool) :
    (rejected removed).HasType [] exits ∧ NestedAdmission.compare? (rejected removed) = .unknown :=
  ⟨rejected_typed removed, by cases removed <;> decide⟩

private def response (removed : Bool) : Op → Value Empty → Unit → Value Empty → Unit → Prop :=
  fun _ _ _ reply _ => reply = if removed then .inl .unit else .inr (.inl .unit)

/-- A reply can send the execution into the removed block. Its outward
branch then takes the first actual exit (index 1 of the inner interface). -/
example : Semantics.Region.Eval (response true) (fun _ => .unit) (rejectedInner true) () 1 .unit () :=
  .cfg (.br .var)
    (.step (label := 0) (by decide) (.case_inl (.op .var rfl) (.br .unit))
      (.step (label := 1) (by decide) (.br .unit) (.exit (label := 3) (by decide))))

/-- A different reply reaches the right-tagged payload at the outer-transfer
index. The right payload is an executable path from the inner entry. -/
example : Semantics.Region.Eval (response false) (fun _ => .unit) (rejectedInner false) () 0 (.inr .unit) () :=
  .cfg (.br .var)
    (.step (label := 0) (by decide) (.case_inr (.op .var rfl) (.case_inl .var (.br (.inr .unit))))
      (.exit (label := 2) (by decide)))

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

/-- Both variants of the existing nested CFG pass the executable check.
Construct the original exact witnesses independently, including their
different outer payload and dead inner slot types. -/
example (roll : IterationRolling C) (loopTag : Bool) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (slots (tagged U)) wideEntry (fun _ => wideRow loopTag) f ∧
      CfgDenotesAt J M (slots (tagged .empty)) wideEntry (fun _ => wideRow loopTag) g ∧ f = g := by
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (slots (tagged U))
    (.br rfl (.inl .unit) : wideEntry.HasType [] (labels (tagged U))) (fun _ => wideRow_typed loopTag U U U)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (slots (tagged .empty))
    (.br rfl (.inl .unit) : wideEntry.HasType [] (labels (tagged .empty)))
    (fun _ => wideRow_typed loopTag .empty .empty .empty)
  have typed (D : Ty Empty) : (original loopTag).HasType [] exits :=
    .cfg (slots (tagged D)) (.br rfl (.inl .unit)) (fun _ => wideRow_typed loopTag D D D)
  have dl : RegionDenotes J M (typed U) f := left.denotes J M
  have dr : RegionDenotes J M (typed .empty) g := right.denotes J M
  have ok : NestedAdmission.compare? (original loopTag) = .certified := by cases loopTag <;> decide
  exact ⟨f, g, left, right, NestedAdmission.compare?_sound J M roll ok dl dr⟩

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedTakenTagFixture
