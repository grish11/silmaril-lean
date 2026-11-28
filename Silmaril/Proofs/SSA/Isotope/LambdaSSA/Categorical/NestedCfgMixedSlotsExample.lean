module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Mixed.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.BlockParameters.Defs
import Mathlib.Tactic.FinCases

/-! # A written outer cycle with a left-tagged and an ordinary retained row -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgMixedSlotsExample

open CategoryTheory CategoryTheory.Limits
open UnusedSummand.BlockParameters (Program)
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
private abbrev tag (D : Ty Empty) : Ty Empty := .coprod U D
private abbrev innerTypes : Fin 1 → Ty Empty := fun _ => U
private def retainedTypes (first : Ty Empty) : Fin 2 → Ty Empty := Fin.cases first (fun _ => Pair)
private def fullTypes (D dead : Ty Empty) : Fin 3 → Ty Empty := Fin.cases (tag D) (Fin.cases dead (fun _ => Pair))
private abbrev labels (first : Ty Empty) := List.ofFn (retainedTypes first) ++ exits

instance : HasTy Op (Ty Empty) where
  src
    | .poll => U
    | .resume => Pair
  trg
    | .poll => .coprod Pair U
    | .resume => .coprod U Pair

private def inner : Program (Φ := Op) innerTypes (labels U) [U] where
  entry := .jump 0 (.var 0 rfl)
  blocks _ := .parameter (.case (.op Op.poll (.var 0 rfl)) (.exit 1 rfl (.var 0 rfl)) (.exit 2 rfl (.var 0 rfl)))

private def guarded : Region Op :=
  .case (.var 0) (inner.region.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 0 (.var 1))

private def ordinary (wide : Bool) : Region Op :=
  .case (.op .resume (.var 0)) (.br 0 (if wide then .inl (.var 0) else .var 0)) (.br 3 (.var 0))

private def start (wide : Bool) : Region Op := .br 0 (if wide then .inl .unit else .unit)

private def keep : Fin 2 ↪ Fin 3 :=
  ⟨fun i => ⟨2 * i.val, by omega⟩, by
    intro i j h
    have eq := congrArg Fin.val h
    apply Fin.ext
    change 2 * i.val = 2 * j.val at eq
    omega⟩

private def compact : CfgRestriction Op 3 :=
  ⟨start true, Fin.cases guarded (Fin.cases (.br 2 .unit) (Fin.cases (ordinary true) Fin.elim0))⟩

private abbrev graph : Region Op := compact.source keep
private def innerKeep : Fin 1 ↪ Fin 1 := Function.Embedding.refl _
private abbrev ordinaryTypes : Fin 1 → Ty Empty := fun _ => Pair

private theorem inner_typed (A : Ty Empty) : inner.region.HasType [U] (labels A) :=
  .cfg innerTypes (.br rfl (.var rfl)) (fun _ =>
    .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl)))

private theorem actualEntry_typed (D dead : Ty Empty) :
    (compact.entry.renameLabels (retainLabelIndex keep)).HasType [] (List.ofFn (fullTypes D dead) ++ exits) :=
  (show (start true).HasType [] (List.ofFn (fun i => fullTypes D dead (keep i)) ++ exits) from
    .br rfl (.inl .unit)).renameLabels (retainLabelRen keep _ _)

private theorem actualRows_typed (D dead : Ty Empty) (i : Fin 3) :
    ((compact.rows i).renameLabels (retainLabelIndex keep)).HasType
      [fullTypes D dead i] (List.ofFn (fullTypes D dead) ++ exits) := by
  let compactLabels := List.ofFn (fun j => fullTypes D dead (keep j)) ++ exits
  have first : guarded.HasType [tag D] compactLabels :=
    .case (.var rfl) ((inner_typed (tag D)).renameVars ((Ren.wk [] (tag D)).lift U)) (.br rfl (.var rfl))
  have second : (ordinary true).HasType [Pair] compactLabels :=
    .case (.op (.var rfl)) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl))
  have omitted : (Region.br 2 .unit : Region Op).HasType [dead] compactLabels := .br rfl .unit
  have ren := retainLabelRen keep (fullTypes D dead) exits
  exact Fin.cases (first.renameLabels ren)
    (Fin.cases (omitted.renameLabels ren) (Fin.cases (second.renameLabels ren) (fun j => Fin.elim0 j))) i

private def replies (exitPair : Bool) : Op → Value Empty → Nat → Value Empty → Nat → Prop
  | .poll, .unit, 0, .inl (.pair .unit .unit), 1 => True
  | .resume, .pair .unit .unit, 1, .inl .unit, 2 => exitPair = false
  | .resume, .pair .unit .unit, 1, .inr (.pair .unit .unit), 2 => exitPair = true
  | .poll, .unit, 2, .inr .unit, 3 => True
  | _, _, _, _, _ => False

/-- The nested request transfers to outer slot two, whose request sends a
tagged reply back to slot zero. The next nested request takes exit zero. -/
example : Semantics.Region.Eval (replies false) (fun _ => .unit) graph 0 0 .unit 3 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies false Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro)) (.br .var))
        (.exit (by decide))))
  · refine .step (label := 2) (next := 0) (middle := .inl .unit) (s₁ := 2) (by decide)
      (.case_inl (.op .var rfl) (.br (.inl .var))) ?_
    refine .step (label := 0) (next := 3) (middle := .unit) (s₁ := 3) (by decide) ?_ (.exit (by decide))
    exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 4) (by decide)
        (.case_inr (.op .var
          (show replies false Op.poll .unit 2 (.inr .unit) 3 from True.intro)) (.br .var))
        (.exit (by decide))))

/-- Another reply from the ordinary row reaches the distinct pair exit. -/
example : Semantics.Region.Eval (replies true) (fun _ => .unit) graph 0 1 (.pair .unit .unit) 2 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies true Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro)) (.br .var))
        (.exit (by decide))))
  · exact .step (label := 2) (next := 4) (by decide)
      (.case_inr (.op .var rfl) (.br .var)) (.exit (by decide))

private def wrongGuarded : Region Op :=
  .case (.var 0) (inner.region.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 2 .unit)

private def wrongOrdinary : Region Op :=
  .case (.op .resume (.var 0)) (.br 0 (.inr (.var 0))) (.br 3 (.var 0))

private def wrong : CfgRestriction Op 3 :=
  ⟨start true, Fin.cases wrongGuarded (Fin.cases (.br 2 .unit) (Fin.cases wrongOrdinary Fin.elim0))⟩

private abbrev wrongGraph : Region Op := wrong.source keep

private theorem wrong_typed : wrongGraph.HasType [] exits := by
  let compactLabels := List.ofFn (fun i => fullTypes U U (keep i)) ++ exits
  have first : wrongGuarded.HasType [tag U] compactLabels :=
    .case (.var rfl) ((inner_typed (tag U)).renameVars ((Ren.wk [] (tag U)).lift U)) (.br rfl .unit)
  have second : wrongOrdinary.HasType [Pair] compactLabels :=
    .case (.op (.var rfl)) (.br rfl (.inr (.var rfl))) (.br rfl (.var rfl))
  have omitted : (Region.br 2 .unit : Region Op).HasType [U] compactLabels := .br rfl .unit
  have ren := retainLabelRen keep (fullTypes U U) exits
  exact .cfg (fullTypes U U) (actualEntry_typed U U) (fun i =>
    Fin.cases (first.renameLabels ren)
      (Fin.cases (omitted.renameLabels ren) (Fin.cases (second.renameLabels ren) (fun j => Fin.elim0 j))) i)

/-- The source graph is exactly typed and passes outer restriction. Its
right-tagged recurrence cannot pass mixed admission. -/
example : wrongGraph.HasType [] exits ∧ (CfgRestriction.check? keep exits.length wrongGraph).isSome = true ∧
    Mixed.compare? keep innerKeep innerTypes ordinaryTypes wrongGraph = .unknown :=
  ⟨wrong_typed, by decide, by decide⟩

/-- The bad tag is selected by a reachable primitive reply. The right arm
of the nested row sends it to the first actual exit. -/
example : Semantics.Region.Eval (replies false) (fun _ => .unit) wrongGraph 0 0 .unit 2 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 3) (by decide)
        (.case_inl (.op .var
          (show replies false Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro)) (.br .var))
        (.exit (by decide))))
  · refine .step (label := 2) (next := 0) (middle := .inr .unit) (s₁ := 2) (by decide)
      (.case_inl (.op .var rfl) (.br (.inr .var))) ?_
    exact .step (label := 0) (next := 3) (by decide) (.case_inr .var (.br .unit)) (.exit (by decide))

namespace MoreOrdinary

private def indexing : Fin 3 → Fin 4 := Fin.cases 2 (Fin.cases 0 (fun _ => 3))

private def mask : Fin 3 ↪ Fin 4 :=
  ⟨indexing, by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

private def types : Fin 2 → Ty Empty := Fin.cases Pair (fun _ => U)
private def fullTypes (D dead : Ty Empty) : Fin 4 → Ty Empty :=
  Fin.cases Pair (Fin.cases dead (Fin.cases (tag D) (fun _ => U)))

private def nested : Region Op :=
  .cfg (.br 0 (.var 0)) 1 (fun _ =>
    .case (.op .poll (.var 0)) (.br 2 (.var 0)) (.br 4 (.var 0)))

private def taggedRow : Region Op :=
  .case (.var 0) (nested.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 0 (.var 1))

private def pairRow : Region Op :=
  .case (.op .resume (.var 0)) (.br 2 (.var 0)) (.br 4 (.var 0))

private def unitRow : Region Op :=
  .case (.op .poll (.var 0)) (.br 4 (.var 0)) (.br 0 (.inl (.var 0)))

private def table : CfgRestriction Op 4 :=
  ⟨.br 0 (.inl .unit), Fin.cases pairRow
    (Fin.cases (.br 3 .unit) (Fin.cases taggedRow (fun _ => unitRow)))⟩

private abbrev graph : Region Op := table.source mask

private def plan : Mixed.Plan Op 2 4 1 1 :=
  (Mixed.check? mask innerKeep innerTypes types graph).get (by decide)

/-- The nested table anchors only the first ordinary row. One worklist
step discovers the second ordinary input through the first row's reply. -/
example : (plan.anchors 0).contains 1 = false ∧ (plan.anchors 1).contains 1 = true :=
  ⟨by decide, by decide⟩

private theorem entry_typed (D dead : Ty Empty) :
    (table.entry.renameLabels (retainLabelIndex mask)).HasType [] (List.ofFn (fullTypes D dead) ++ exits) :=
  (show table.entry.HasType [] (List.ofFn (fun i => fullTypes D dead (mask i)) ++ exits) from
    .br rfl (.inl .unit)).renameLabels (retainLabelRen mask _ _)

private theorem rows_typed (D dead : Ty Empty) (i : Fin 4) :
    ((table.rows i).renameLabels (retainLabelIndex mask)).HasType
      [fullTypes D dead i] (List.ofFn (fullTypes D dead) ++ exits) := by
  let localLabels := List.ofFn (fun i => fullTypes D dead (mask i)) ++ exits
  have first : pairRow.HasType [Pair] localLabels :=
    .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  have omitted : (Region.br 3 .unit : Region Op).HasType [dead] localLabels := .br rfl .unit
  have innerTyped : nested.HasType [U] localLabels :=
    .cfg innerTypes (.br rfl (.var rfl)) (fun _ =>
      .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl)))
  have known : taggedRow.HasType [tag D] localLabels :=
    .case (.var rfl) (innerTyped.renameVars ((Ren.wk [] (tag D)).lift U)) (.br rfl (.var rfl))
  have last : unitRow.HasType [U] localLabels :=
    .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.inl (.var rfl)))
  have ren := retainLabelRen mask (fullTypes D dead) exits
  exact Fin.cases (first.renameLabels ren) (Fin.cases (omitted.renameLabels ren)
    (Fin.cases (known.renameLabels ren) (fun _ => last.renameLabels ren))) i

private def responses : Op → Value Empty → Nat → Value Empty → Nat → Prop
  | .poll, .unit, 0, .inl (.pair .unit .unit), 1 => True
  | .resume, .pair .unit .unit, 1, .inl .unit, 2 => True
  | .poll, .unit, 2, .inr .unit, 3 => True
  | .poll, .unit, 3, .inr .unit, 4 => True
  | _, _, _, _, _ => False

/-- The nested row is at written slot two. Its reply visits slots zero
and three before a tagged backedge enters slot two again. -/
example : Semantics.Region.Eval responses (fun _ => .unit) graph 0 0 .unit 4 := by
  refine .cfg (.br (.inl .unit)) ?_
  refine .step (label := 2) (next := 0) (middle := .pair .unit .unit) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 1) (by decide)
        (.case_inl (.op .var
          (show responses Op.poll .unit 0 (.inl (.pair .unit .unit)) 1 from True.intro)) (.br .var))
        (.exit (by decide))))
  · refine .step (label := 0) (next := 3) (middle := .unit) (s₁ := 2) (by decide)
      (.case_inl (.op .var (show responses Op.resume (.pair .unit .unit) 1 (.inl .unit) 2 from True.intro))
        (.br .var)) ?_
    refine .step (label := 3) (next := 2) (middle := .inl .unit) (s₁ := 3) (by decide)
      (.case_inr (.op .var (show responses Op.poll .unit 2 (.inr .unit) 3 from True.intro))
        (.br (.inl .var))) ?_
    refine .step (label := 2) (next := 4) (middle := .unit) (s₁ := 4) (by decide) ?_ (.exit (by decide))
    exact .case_inl .var (.cfg (.br .var)
      (.step (label := 0) (next := 5) (by decide)
        (.case_inr (.op .var (show responses Op.poll .unit 3 (.inr .unit) 4 from True.intro)) (.br .var))
        (.exit (by decide))))

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (fullTypes U U) (table.entry.renameLabels (retainLabelIndex mask))
        (fun i => (table.rows i).renameLabels (retainLabelIndex mask)) f ∧
      CfgDenotesAt J M (fullTypes .empty .empty) (table.entry.renameLabels (retainLabelIndex mask))
        (fun i => (table.rows i).renameLabels (retainLabelIndex mask)) g ∧ f = g := by
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (fullTypes U U) (entry_typed U U) (rows_typed U U)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (fullTypes .empty .empty)
    (entry_typed .empty .empty) (rows_typed .empty .empty)
  have tl : graph.HasType [] exits := .cfg (fullTypes U U) (entry_typed U U) (rows_typed U U)
  have tr : graph.HasType [] exits := .cfg (fullTypes .empty .empty)
    (entry_typed .empty .empty) (rows_typed .empty .empty)
  have dl : RegionDenotes J M tl f := left.denotes J M
  have dr : RegionDenotes J M tr g := right.denotes J M
  have ok : Mixed.compare? mask innerKeep innerTypes types graph = .certified := by decide
  exact ⟨f, g, left, right, Mixed.compare?_sound J M roll ok dl dr⟩

end Model

end MoreOrdinary

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

/-- The original #4860 program certifies directly. The denotation witnesses
still use the full written table and choose different right and dead types. -/
example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (fullTypes U U) (compact.entry.renameLabels (retainLabelIndex keep))
        (fun i => (compact.rows i).renameLabels (retainLabelIndex keep)) f ∧
      CfgDenotesAt J M (fullTypes .empty .empty) (compact.entry.renameLabels (retainLabelIndex keep))
        (fun i => (compact.rows i).renameLabels (retainLabelIndex keep)) g ∧ f = g := by
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (fullTypes U U) (actualEntry_typed U U) (actualRows_typed U U)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (fullTypes .empty .empty)
    (actualEntry_typed .empty .empty) (actualRows_typed .empty .empty)
  have tl : graph.HasType [] exits := .cfg (fullTypes U U) (actualEntry_typed U U) (actualRows_typed U U)
  have tr : graph.HasType [] exits := .cfg (fullTypes .empty .empty)
    (actualEntry_typed .empty .empty) (actualRows_typed .empty .empty)
  have dl : RegionDenotes J M tl f := left.denotes J M
  have dr : RegionDenotes J M tr g := right.denotes J M
  have ok : Mixed.compare? keep innerKeep innerTypes ordinaryTypes graph = .certified := by decide
  exact ⟨f, g, left, right, Mixed.compare?_sound J M roll ok dl dr⟩

end Model

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgMixedSlotsExample
