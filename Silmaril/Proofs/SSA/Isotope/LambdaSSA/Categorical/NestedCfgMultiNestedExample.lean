module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.MultiNested.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
import Mathlib.Tactic.FinCases

/-! # Two independently written nested rows exchange oppositely tagged replies -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgMultiNestedExample

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open NestedAdmission (exits)
open NestedAdmission.Finite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private inductive Op where
  | poll
  | resume

private abbrev U : Ty Empty := .unit
private abbrev Pair : Ty Empty := .product U U

instance : HasTy Op (Ty Empty) where
  src
    | .poll => U
    | .resume => Pair
  trg
    | .poll => .coprod Pair U
    | .resume => .coprod U Pair

private def index : Fin 3 → Fin 4 := Fin.cases 0 (Fin.cases 2 (fun _ => 3))
private def keep : Fin 3 ↪ Fin 4 :=
  ⟨index, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

private def types : Fin 3 → Ty Empty := Fin.cases U (fun _ => Pair)
private def forms : Fin 3 → Bool := Fin.cases true (Fin.cases true (fun _ => false))

private def choices : Fin 3 → CaseTag := Fin.cases .inl (Fin.cases .inr (fun _ => .inl))

private def wide (D E dead : Ty Empty) (tag : CaseTag := .inl) : Fin 4 → Ty Empty :=
  Fin.cases (.coprod U D) (Fin.cases dead (Fin.cases (tag.sumType Pair E) (fun _ => Pair)))

private def outerGuard (body : Region Op) (tag : CaseTag := .inl) : Region Op :=
  let arm := body.renameVars (Silmaril.DeBruijn.lift Nat.succ)
  match tag with
  | .inl => .case (.var 0) arm (.br 3 .unit)
  | .inr => .case (.var 0) (.br 3 .unit) arm

private def incomingTag (wrong : Bool) (tag : CaseTag) : CaseTag :=
  if wrong then (match tag with | .inl => .inr | .inr => .inl) else tag

private def first (wrong : Bool) (tag : CaseTag) : Region Op :=
  .cfg (.br 0 (.var 0)) 1 (fun _ =>
    .case (.op .poll (.var 0))
      (.br 2 ((incomingTag wrong tag).inject (.var 0))) (.br 4 (.var 0)))

private def second : Region Op :=
  .cfg (.br 0 (.var 0)) 1 (fun _ =>
    .case (.op .resume (.var 0)) (.br 1 (.inl (.var 0))) (.br 3 (.var 0)))

private def ordinary : Region Op :=
  .case (.op .resume (.var 0)) (.br 0 (.inl (.var 0))) (.br 4 (.var 0))

private def table (wrong : Bool) (tag : CaseTag := .inl) : CfgRestriction Op 4 :=
  ⟨.br 0 (.inl .unit), Fin.cases (outerGuard (first wrong tag))
    (Fin.cases (.br 3 .unit) (Fin.cases (outerGuard second tag) (fun _ => ordinary)))⟩

private abbrev graph (wrong : Bool) := (table wrong .inr).source keep

private def plan : MultiNested.Plan Op 3 4 :=
  (MultiNested.check? keep types forms (graph false) (tags := choices)).get (by decide)

/-- One step anchors the second nested payload. Its different reply
then anchors the ordinary slot. -/
example : (plan.anchors 0).contains 1 = false ∧ (plan.anchors 1).contains 1 = true ∧
    (plan.anchors 1).contains 2 = false ∧ (plan.anchors 2).contains 2 = true := by decide

private theorem entry_typed (wrong : Bool) (D E dead : Ty Empty) (tag : CaseTag := .inl) :
    ((table wrong tag).entry.renameLabels (retainLabelIndex keep)).HasType []
      (List.ofFn (wide D E dead tag) ++ exits) :=
  (show (table wrong tag).entry.HasType [] (List.ofFn (fun i => wide D E dead tag (keep i)) ++ exits) from
    .br rfl (.inl .unit)).renameLabels (retainLabelRen keep _ _)

private theorem rows_typed (wrong : Bool) (D E dead : Ty Empty) (badType : wrong = true → E = Pair) (i : Fin 4)
    (tag : CaseTag := .inl) :
    (((table wrong tag).rows i).renameLabels (retainLabelIndex keep)).HasType
      [wide D E dead tag i] (List.ofFn (wide D E dead tag) ++ exits) := by
  let L := List.ofFn (fun i => wide D E dead tag (keep i)) ++ exits
  have row0 : (first wrong tag).HasType [U] L := by
    refine .cfg (fun _ => U) (.br rfl (.var rfl)) (fun _ => .case (.op (.var rfl)) ?_ (.br rfl (.var rfl)))
    cases wrong
    · cases tag
      · exact .br rfl (.inl (.var rfl))
      · exact .br rfl (.inr (.var rfl))
    · have eq := badType rfl
      subst E
      cases tag
      · exact .br rfl (.inr (.var rfl))
      · exact .br rfl (.inl (.var rfl))
  have row2 : second.HasType [Pair] L :=
    .cfg (fun _ => Pair) (.br rfl (.var rfl)) (fun _ =>
      .case (.op (.var rfl)) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl)))
  have guard {A T : Ty Empty} (side : CaseTag) {body : Region Op} (typed : body.HasType [A] L) :
      (outerGuard body side).HasType [side.sumType A T] L := by
    cases side
    · exact .case (.var rfl) (typed.renameVars ((Ren.wk [] (.coprod A T)).lift A)) (.br rfl .unit)
    · exact .case (.var rfl) (.br rfl .unit) (typed.renameVars ((Ren.wk [] (.coprod T A)).lift A))
  have deadRow : (Region.br 3 .unit : Region Op).HasType [dead] L := .br rfl .unit
  have ord : ordinary.HasType [Pair] L :=
    .case (.op (.var rfl)) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl))
  have ren := retainLabelRen keep (wide D E dead tag) exits
  exact Fin.cases ((guard .inl row0).renameLabels ren)
    (Fin.cases (deadRow.renameLabels ren) (Fin.cases ((guard tag row2).renameLabels ren)
      (fun _ => ord.renameLabels ren))) i

/-- The wrong inter-nested tag survives exact typing and the outer target
restriction. The route checker returns unknown. -/
example : (graph true).HasType [] exits ∧ (CfgRestriction.check? keep exits.length (graph true)).isSome = true ∧
    MultiNested.compare? keep types forms (graph true) (tags := choices) = .unknown :=
  ⟨.cfg (wide U Pair U .inr) (entry_typed true U Pair U .inr)
    (fun i => rows_typed true U Pair U (fun _ => rfl) i .inr), by decide, by decide⟩

private def replies (back : Bool) : Op → Value Empty → Nat → Value Empty → Nat → Prop
  | .poll, .unit, 0, .inl (.pair .unit .unit), 1 => True
  | .resume, .pair .unit .unit, 1, .inl .unit, 2 => back = true
  | .resume, .pair .unit .unit, 1, .inr (.pair .unit .unit), 2 => back = false
  | .poll, .unit, 2, .inr .unit, 3 => True
  | .resume, .pair .unit .unit, 2, .inr (.pair .unit .unit), 3 => True
  | _, _, _, _, _ => False

/-- Written slot zero sends a right injection to slot two, which sends a left injection back. -/
example : Semantics.Region.Eval (replies true) (fun _ => .unit) (graph false) 0 0 .unit 3 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .inr (.pair .unit .unit)) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies true Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro))
          (.br (.inr .var))) (.exit (by decide))))
  · refine .step (label := 2) (next := 0) (middle := .inl .unit) (s₁ := 2) (by decide) ?_ ?_
    · exact .case_inr .var (.cfg (.br .var)
        (.step (label := 0) (next := 1) (by decide)
          (.case_inl (.op .var
            (show replies true Op.resume (.pair .unit .unit) 1 (.inl .unit) 2 from rfl))
            (.br (.inl .var))) (.exit (by decide))))
    · refine .step (label := 0) (next := 4) (middle := .unit) (s₁ := 3) (by decide) ?_ (.exit (by decide))
      exact .case_inl .var (.cfg (.br .var)
        (.step (label := 0) (next := 5) (by decide)
          (.case_inr (.op .var
            (show replies true Op.poll .unit 2 (.inr .unit) 3 from True.intro)) (.br .var)) (.exit (by decide))))

/-- The second nested reply can instead enter ordinary slot three and take the pair exit. -/
example : Semantics.Region.Eval (replies false) (fun _ => .unit) (graph false) 0 1 (.pair .unit .unit) 3 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .inr (.pair .unit .unit)) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies false Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro))
          (.br (.inr .var))) (.exit (by decide))))
  · refine .step (label := 2) (next := 3) (middle := .pair .unit .unit) (s₁ := 2) (by decide) ?_ ?_
    · exact .case_inr .var (.cfg (.br .var)
        (.step (label := 0) (next := 4) (by decide)
          (.case_inr (.op .var
            (show replies false Op.resume (.pair .unit .unit) 1 (.inr (.pair .unit .unit)) 2 from rfl))
            (.br .var)) (.exit (by decide))))
    · exact .step (label := 3) (next := 5) (by decide)
        (.case_inr (.op .var
          (show replies false Op.resume (.pair .unit .unit) 2 (.inr (.pair .unit .unit)) 3 from True.intro))
          (.br .var)) (.exit (by decide))

/-- The wrong tag follows the same first request to slot two and takes its left arm. -/
example : Semantics.Region.Eval (replies true) (fun _ => .unit) (graph true) 0 0 .unit 1 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .inl (.pair .unit .unit)) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies true Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro))
          (.br (.inl .var))) (.exit (by decide))))
  · exact .step (label := 2) (next := 4) (by decide) (.case_inl .var (.br .unit)) (.exit (by decide))

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

/-- Both exact witnesses are of the original full graph. The inactive
summands of both nested slots and the omitted outer input type vary. -/
example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (wide U Pair U .inr) ((table false .inr).entry.renameLabels (retainLabelIndex keep))
        (fun i => ((table false .inr).rows i).renameLabels (retainLabelIndex keep)) f ∧
      CfgDenotesAt J M (wide .empty .empty .empty .inr) ((table false .inr).entry.renameLabels (retainLabelIndex keep))
        (fun i => ((table false .inr).rows i).renameLabels (retainLabelIndex keep)) g ∧ f = g := by
  have leftRows := fun i => rows_typed false U Pair U (fun _ => rfl) i .inr
  have rightRows := fun i => rows_typed false .empty .empty .empty (by intro h; cases h) i .inr
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (wide U Pair U .inr)
    (entry_typed false U Pair U .inr) leftRows
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (wide .empty .empty .empty .inr)
    (entry_typed false .empty .empty .empty .inr) rightRows
  have tl : (graph false).HasType [] exits := .cfg (wide U Pair U .inr)
    (entry_typed false U Pair U .inr) leftRows
  have tr : (graph false).HasType [] exits := .cfg (wide .empty .empty .empty .inr)
    (entry_typed false .empty .empty .empty .inr) rightRows
  have dl : RegionDenotes J M tl f := left.denotes J M
  have dr : RegionDenotes J M tr g := right.denotes J M
  have ok : MultiNested.compare? keep types forms (graph false) (tags := choices) = .certified := by decide
  exact ⟨f, g, left, right, MultiNested.compare?_sound J M roll ok dl dr⟩

end Model

namespace SparseInner

private def keepLocal : Fin 2 ↪ Fin 3 :=
  ⟨fun i => ⟨2 * i.val, by omega⟩, by
    intro i j h
    have eq := congrArg Fin.val h
    apply Fin.ext
    change 2 * i.val = 2 * j.val at eq
    omega⟩

private def payloads : Fin 2 → Ty Empty := Fin.cases U (fun _ => Pair)
private def innerTypes (dead : Ty Empty) : Fin 3 → Ty Empty := Fin.cases U (Fin.cases dead (fun _ => Pair))

private def masks : Fin 3 → Option MultiNested.InnerMask :=
  Fin.cases (some ⟨1, 2, keepLocal, payloads⟩) (fun _ => none)

private def entry : Region Op := .br 0 (.var 0)
private def pollRow : Region Op := .case (.op .poll (.var 0)) (.br 1 (.var 0)) (.br 5 (.var 0))
private def resumeRow : Region Op := .case (.op .resume (.var 0)) (.br 0 (.var 0)) (.br 3 (.inl (.var 0)))
private def deadRow : Region Op := .br 5 .unit

private def innerRows (wrong : Bool) : Fin 3 → Region Op :=
  let reindex := retainLabelIndex keepLocal
  Fin.cases (if wrong then .case (.op .poll (.var 0)) (.br 1 (.var 0)) (.br 6 (.var 0))
      else pollRow.renameLabels reindex)
    (Fin.cases (deadRow.renameLabels reindex) (fun _ => resumeRow.renameLabels reindex))

private def innerBody (wrong : Bool) : Region Op :=
  .cfg (entry.renameLabels (retainLabelIndex keepLocal)) 3 (innerRows wrong)

private def fullTable (wrong : Bool) : CfgRestriction Op 4 :=
  { table false with rows := Fin.cases (outerGuard (innerBody wrong)) (fun i => (table false).rows i.succ) }

private abbrev graph (wrong : Bool) := (fullTable wrong).source keep

private theorem fullRows_typed (wrong : Bool) (D E deadOuter deadInner : Ty Empty)
    (badType : wrong = true → deadInner = Pair) (i : Fin 4) :
    (((fullTable wrong).rows i).renameLabels (retainLabelIndex keep)).HasType
      [wide D E deadOuter .inl i] (List.ofFn (wide D E deadOuter) ++ exits) := by
  let L := List.ofFn (fun i => wide D E deadOuter .inl (keep i)) ++ exits
  let localLabels := List.ofFn (fun i => innerTypes deadInner (keepLocal i)) ++ L
  have ren := retainLabelRen keepLocal (innerTypes deadInner) L
  have ent : entry.HasType [U] localLabels := .br rfl (.var rfl)
  have poll : pollRow.HasType [U, U] localLabels :=
    .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  have resume : resumeRow.HasType [Pair, U] localLabels :=
    .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.inl (.var rfl)))
  have omitted : deadRow.HasType [deadInner, U] localLabels := .br rfl .unit
  have first : (innerRows wrong 0).HasType [U, U] (List.ofFn (innerTypes deadInner) ++ L) := by
    cases wrong
    · exact poll.renameLabels ren
    · have eq := badType rfl
      subst deadInner
      exact .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  have nested : (innerBody wrong).HasType [U] L :=
    .cfg (innerTypes deadInner) (ent.renameLabels ren) (Fin.cases first
      (Fin.cases (omitted.renameLabels ren) (fun _ => resume.renameLabels ren)))
  have guarded : (outerGuard (innerBody wrong)).HasType [.coprod U D] L :=
    .case (.var rfl) (nested.renameVars ((Ren.wk [] (.coprod U D)).lift U)) (.br rfl .unit)
  exact Fin.cases (guarded.renameLabels (retainLabelRen keep _ _))
    (fun j => rows_typed false D E deadOuter (by intro h; cases h) j.succ) i

/-- The bad source edge reaches a well-typed inner slot that the supplied
inner mask omits. The full outer restriction still succeeds. -/
example : (graph true).HasType [] exits ∧
    (CfgRestriction.check? keep exits.length (graph true)).isSome = true ∧
    CfgRestriction.check? keepLocal (3 + exits.length) (innerBody true) = none ∧
    MultiNested.compare? keep types forms (graph true) exits masks = .unknown :=
  ⟨.cfg (wide U Pair U) (entry_typed false U Pair U)
    (fullRows_typed true U Pair U Pair (fun _ => rfl)), by decide, rfl, by decide⟩

private def responses (stop : Bool) : Op → Value Empty → Nat → Value Empty → Nat → Prop
  | .poll, .unit, 0, .inl (.pair .unit .unit), 1 => True
  | .resume, .pair .unit .unit, 1, .inl .unit, 2 => True
  | .poll, .unit, 2, .inl (.pair .unit .unit), 3 => stop = false
  | .poll, .unit, 2, .inr .unit, 3 => stop = true
  | .resume, .pair .unit .unit, 3, .inr (.pair .unit .unit), 4 => True
  | .resume, .pair .unit .unit, 4, .inr (.pair .unit .unit), 5 => True
  | .resume, .pair .unit .unit, 5, .inr (.pair .unit .unit), 6 => True
  | _, _, _, _, _ => False

/-- In the first written inner graph, visit local slots zero and two,
return to zero, then take actual exit ordinal zero. -/
example : Semantics.Region.Eval (responses true) (fun _ => .unit) (graph false) 0 0 .unit 3 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 4) (middle := .unit) (s₁ := 3) (by decide) ?_ (.exit (by decide))
  refine .case_inl .var (.cfg (.br .var) ?_)
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 1) (by decide)
    (.case_inl (.op .var
      (show responses true Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro)) (.br .var)) ?_
  refine .step (label := 2) (next := 0) (middle := .unit) (s₁ := 2) (by decide)
    (.case_inl (.op .var
      (show responses true Op.resume (.pair .unit .unit) 1 (.inl .unit) 2 from True.intro)) (.br .var)) ?_
  exact .step (label := 0) (next := 7) (by decide)
    (.case_inr (.op .var (show responses true Op.poll .unit 2 (.inr .unit) 3 from rfl)) (.br .var)) (.exit (by decide))

/-- The same local backedge can lead to the second nested outer row.
Its reply enters the ordinary row and takes actual exit ordinal one. -/
example : Semantics.Region.Eval (responses false) (fun _ => .unit) (graph false) 0 1 (.pair .unit .unit) 6 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .inl (.pair .unit .unit)) (s₁ := 4) (by decide) ?_ ?_
  · refine .case_inl .var (.cfg (.br .var) ?_)
    refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 1) (by decide)
      (.case_inl (.op .var
        (show responses false Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro)) (.br .var)) ?_
    refine .step (label := 2) (next := 0) (middle := .unit) (s₁ := 2) (by decide)
      (.case_inl (.op .var
        (show responses false Op.resume (.pair .unit .unit) 1 (.inl .unit) 2 from True.intro)) (.br .var)) ?_
    refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 3) (by decide)
      (.case_inl (.op .var
        (show responses false Op.poll .unit 2 (.inl (.pair .unit .unit)) 3 from rfl)) (.br .var)) ?_
    exact .step (label := 2) (next := 5) (by decide)
      (.case_inr (.op .var
        (show responses false Op.resume (.pair .unit .unit) 3 (.inr (.pair .unit .unit)) 4 from True.intro))
        (.br (.inl .var))) (.exit (by decide))
  · refine .step (label := 2) (next := 3) (middle := .pair .unit .unit) (s₁ := 5) (by decide) ?_ ?_
    · exact .case_inl .var (.cfg (.br .var)
        (.step (label := 0) (next := 4) (by decide)
          (.case_inr (.op .var
            (show responses false Op.resume (.pair .unit .unit) 4 (.inr (.pair .unit .unit)) 5 from True.intro))
            (.br .var)) (.exit (by decide))))
    · exact .step (label := 3) (next := 5) (by decide)
        (.case_inr (.op .var
          (show responses false Op.resume (.pair .unit .unit) 5 (.inr (.pair .unit .unit)) 6 from True.intro))
          (.br .var)) (.exit (by decide))

/-- On the rejected source, the first reply actually enters the omitted inner block. -/
example : Semantics.Region.Eval (responses true) (fun _ => .unit) (graph true) 0 0 .unit 1 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 4) (middle := .unit) (s₁ := 1) (by decide) ?_ (.exit (by decide))
  refine .case_inl .var (.cfg (.br .var) ?_)
  refine .step (label := 0) (next := 1) (middle := .pair .unit .unit) (s₁ := 1) (by decide)
    (.case_inl (.op .var
      (show responses true Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro)) (.br .var)) ?_
  exact .step (label := 1) (next := 7) (by decide) (.br .unit) (.exit (by decide))

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

/-- The two exact full witnesses vary the outer right summands and the
omitted outer and inner slot types. -/
example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (wide U Pair U) ((fullTable false).entry.renameLabels (retainLabelIndex keep))
        (fun i => ((fullTable false).rows i).renameLabels (retainLabelIndex keep)) f ∧
      CfgDenotesAt J M (wide .empty .empty .empty) ((fullTable false).entry.renameLabels (retainLabelIndex keep))
        (fun i => ((fullTable false).rows i).renameLabels (retainLabelIndex keep)) g ∧ f = g := by
  have leftRows := fullRows_typed false U Pair U Pair (fun _ => rfl)
  have rightRows := fullRows_typed false .empty .empty .empty .empty (by intro h; cases h)
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (wide U Pair U) (entry_typed false U Pair U) leftRows
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (wide .empty .empty .empty)
    (entry_typed false .empty .empty .empty) rightRows
  have tl : (graph false).HasType [] exits := .cfg (wide U Pair U) (entry_typed false U Pair U) leftRows
  have tr : (graph false).HasType [] exits := .cfg (wide .empty .empty .empty)
    (entry_typed false .empty .empty .empty) rightRows
  have dl : RegionDenotes J M tl f := left.denotes J M
  have dr : RegionDenotes J M tr g := right.denotes J M
  have ok : MultiNested.compare? keep types forms (graph false) exits masks = .certified := by decide
  exact ⟨f, g, left, right, MultiNested.compare?_sound J M roll ok dl dr⟩

end Model

end SparseInner

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgMultiNestedExample
