module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Outer.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-! # Two heterogeneous inner states with an omitted middle slot -/

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgFiniteAdmissionExample

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open NestedAdmission (exits)

private inductive Op where
  | unitRequest
  | pairRequest

private abbrev U := NestedAdmission.unitTy
private abbrev Pair := NestedAdmission.pairTy
private abbrev tag (D : Ty Empty) : Ty Empty := .coprod U D
private abbrev slots (A : Ty Empty) : Fin 1 → Ty Empty := fun _ => A
private abbrev labels (A : Ty Empty) : LCtx (Ty Empty) := List.ofFn (slots A) ++ exits

instance : HasTy Op (Ty Empty) where
  src
    | .unitRequest => U
    | .pairRequest => Pair
  trg
    | .unitRequest => .coprod Pair (.coprod U U)
    | .pairRequest => .coprod U Pair

private def keep : Fin 2 ↪ Fin 3 :=
  ⟨fun i => ⟨2 * i.val, by omega⟩, by
    intro i j h
    have eq := congrArg Fin.val h
    apply Fin.ext
    change 2 * i.val = 2 * j.val at eq
    omega⟩

private def types : Fin 2 → Ty Empty := Fin.cases U (fun _ => Pair)
private def family (dead : Ty Empty) : Fin 3 → Ty Empty := Fin.cases U (Fin.cases dead (fun _ => Pair))

private def innerEntry : Region Op := .br 0 (.var 0)

private def fromUnit (next : Region Op) : Region Op :=
  .case (.op .unitRequest (.var 0)) next
    (.case (.var 0) (.br 2 (.inl (.var 0))) (.br 3 (.var 0)))

private def fromPair : Region Op :=
  .case (.op .pairRequest (.var 0)) (.br 0 (.var 0)) (.br 4 (.var 0))

private def dead : Region Op := .br 3 .unit

private def actualEntry : Region Op := innerEntry.renameLabels (retainLabelIndex keep)

private def rows (bad : Bool) : Fin 3 → Region Op :=
  Fin.cases (if bad then
    .case (.op .unitRequest (.var 0)) (.br 1 .unit)
      (.case (.var 0) (.br 3 (.inl (.var 0))) (.br 4 (.var 0)))
    else (fromUnit (.br 1 (.var 0))).renameLabels (retainLabelIndex keep))
    (Fin.cases (dead.renameLabels (retainLabelIndex keep)) (fun _ => fromPair.renameLabels (retainLabelIndex keep)))

private def guarded (body : Region Op) : Region Op :=
  .case (.var 0) (body.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 0 (.var 1))

private def outerRow (bad : Bool) : Region Op := guarded (.cfg actualEntry 3 (rows bad))
private def start : Region Op := .br 0 (.inl .unit)
private def original (bad : Bool) : Region Op := .cfg start 1 (fun _ => outerRow bad)

private theorem actualEntry_typed (D deadTy : Ty Empty) :
    actualEntry.HasType [U] (List.ofFn (family deadTy) ++ labels (tag D)) :=
  (show innerEntry.HasType [U] (List.ofFn (fun i => family deadTy (keep i)) ++ labels (tag D)) from
    .br rfl (.var rfl)).renameLabels (retainLabelRen keep _ _)

private theorem row_typed (D deadTy : Ty Empty) (i : Fin 3) :
    (rows false i).HasType [family deadTy i, U] (List.ofFn (family deadTy) ++ labels (tag D)) := by
  let L := List.ofFn (fun i => family deadTy (keep i)) ++ labels (tag D)
  have ren := retainLabelRen keep (family deadTy) (labels (tag D))
  have h0 : (fromUnit (.br 1 (.var 0))).HasType [U, U] L :=
    .case (.op (.var rfl)) (.br rfl (.var rfl))
      (.case (.var rfl) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl)))
  have h1 : dead.HasType [deadTy, U] L := .br rfl .unit
  have h2 : fromPair.HasType [Pair, U] L :=
    .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  exact Fin.cases (h0.renameLabels ren)
    (Fin.cases (h1.renameLabels ren) (fun _ => h2.renameLabels ren)) i

private theorem outer_typed (bad : Bool) (D deadTy : Ty Empty) (allowed : bad = true → deadTy = U) :
    (outerRow bad).HasType [tag D] (labels (tag D)) := by
  have inner : (Region.cfg actualEntry 3 (rows bad)).HasType [U] (labels (tag D)) := by
    refine .cfg (family deadTy) (actualEntry_typed D deadTy) ?_
    cases bad
    · exact row_typed D deadTy
    · rw [allowed rfl]
      intro i
      refine Fin.cases ?_ (fun j => row_typed D U j.succ) i
      exact .case (.op (.var rfl)) (.br rfl .unit)
        (.case (.var rfl) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl)))
  exact .case (.var rfl) (inner.renameVars ((Ren.wk [] (tag D)).lift U)) (.br rfl (.var rfl))

/-- The first request can name the omitted middle slot. Its exact typing
survives, but the finite comparison reports unknown. -/
example : (original true).HasType [] exits ∧
    NestedAdmission.Finite.compare? keep types (original true) = .unknown :=
  ⟨.cfg (slots (tag U)) (.br rfl (.inl .unit)) (fun _ => outer_typed true U U (fun _ => rfl)), by decide⟩

private def replies : Op → Value Empty → Nat → Value Empty → Nat → Prop
  | .unitRequest, .unit, 0, .inl (.pair .unit .unit), 1 => True
  | .pairRequest, .pair .unit .unit, 1, .inl .unit, 2 => True
  | .unitRequest, .unit, 2, .inr (.inr .unit), 3 => True
  | _, _, _, _, _ => False

/-- The original inner graph visits slots zero, two, and zero in sequence
before taking the first actual exit. The two payloads cross both requests. -/
example : Semantics.Region.Eval replies (fun _ => .unit) (.cfg actualEntry 3 (rows false)) 0 1 .unit 3 := by
  refine .cfg (.br .var) ?_
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := 1) (by decide) ?_ ?_
  · exact .case_inl (.op .var (by trivial)) (.br .var)
  · refine .step (label := 2) (next := 0) (middle := .unit) (s₁ := 2) (by decide) ?_ ?_
    · exact .case_inl (.op .var (by trivial)) (.br .var)
    · refine .step (label := 0) (next := 4) (middle := .unit) (s₁ := 3) (by decide) ?_ (.exit (by decide))
      exact .case_inr (.op .var (by trivial)) (.case_inr .var (.br .var))

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M exits)

/-- Both original exact witnesses retain slots zero and two. Their requests
consume Unit and Unit × Unit respectively and can transfer to the other
retained slot. The omitted middle type and the outer right summand vary. -/
example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (slots (tag U)) start (fun _ => outerRow false) f ∧
      CfgDenotesAt J M (slots (tag .empty)) start (fun _ => outerRow false) g ∧ f = g := by
  have rowLeft := outer_typed false U U (by intro h; cases h)
  have rowRight := outer_typed false .empty .empty (by intro h; cases h)
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (slots (tag U))
    (.br rfl (.inl .unit) : start.HasType [] (labels (tag U))) (fun _ => rowLeft)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (slots (tag .empty))
    (.br rfl (.inl .unit) : start.HasType [] (labels (tag .empty))) (fun _ => rowRight)
  have ok : NestedAdmission.Finite.compare? keep types (original false) = .certified := by decide
  have typedLeft : (original false).HasType [] exits :=
    .cfg (slots (tag U)) (.br rfl (.inl .unit)) (fun _ => rowLeft)
  have typedRight : (original false).HasType [] exits :=
    .cfg (slots (tag .empty)) (.br rfl (.inl .unit)) (fun _ => rowRight)
  have dl : RegionDenotes J M typedLeft f := left.denotes J M
  have dr : RegionDenotes J M typedRight g := right.denotes J M
  exact ⟨f, g, left, right, NestedAdmission.Finite.compare?_sound J M roll ok dl dr⟩

end Model

namespace OrderedExits

private def boundary (wrong : Bool) : LCtx (Ty Empty) := [U, if wrong then Pair else U, Pair]
private abbrev outerLabels (T : Ty Empty) (wrong : Bool) := List.ofFn (slots T) ++ boundary wrong
private abbrev taggedPair (D : Ty Empty) : Ty Empty := .coprod Pair D

private def enter : Region Op := .br 0 .unit

private def unitRow (wrong : Bool) : Region Op :=
  .case (.op .unitRequest (.var 0)) (.br 1 (.var 0))
    (.case (.var 0) (.br 3 (.var 0)) (.br 4 (if wrong then .pair (.var 0) .unit else .var 0)))

private def pairRow : Region Op :=
  .case (.op .pairRequest (.var 0)) (.br 2 (.inl (.var 2))) (.br 5 (.var 0))

private def originalEntry := enter.renameLabels (retainLabelIndex keep)

private def originalRows (wrong : Bool) : Fin 3 → Region Op :=
  let reindex := retainLabelIndex keep
  Fin.cases ((unitRow wrong).renameLabels reindex)
    (Fin.cases (dead.renameLabels reindex) (fun _ => pairRow.renameLabels reindex))

private def guardedRow (wrong : Bool) : Region Op := guarded (.cfg originalEntry 3 (originalRows wrong))
private def start : Region Op := .br 0 (.inl (.pair .unit .unit))
private def graph (wrong : Bool) : Region Op := .cfg start 1 (fun _ => guardedRow wrong)

private theorem guardedRow_typed (wrong : Bool) (D deadTy : Ty Empty) :
    (guardedRow wrong).HasType [taggedPair D] (outerLabels (taggedPair D) wrong) := by
  let L := outerLabels (taggedPair D) wrong
  let compact := List.ofFn (fun i => family deadTy (keep i)) ++ L
  have ren := retainLabelRen keep (family deadTy) L
  have initial : enter.HasType [Pair] compact := .br rfl .unit
  have first : (unitRow wrong).HasType [U, Pair] compact := by
    refine .case (.op (.var rfl)) (.br rfl (.var rfl))
      (.case (.var rfl) (.br rfl (.var rfl)) ?_)
    cases wrong
    · exact .br rfl (.var rfl)
    · exact .br rfl (.pair (.var rfl) .unit)
  have middle : dead.HasType [deadTy, Pair] compact := .br rfl .unit
  have second : pairRow.HasType [Pair, Pair] compact :=
    .case (.op (.var rfl)) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl))
  have blocks : ∀ i, (originalRows wrong i).HasType [family deadTy i, Pair]
      (List.ofFn (family deadTy) ++ L) :=
    Fin.cases (first.renameLabels ren)
      (Fin.cases (middle.renameLabels ren) (fun _ => second.renameLabels ren))
  have inner : (Region.cfg originalEntry 3 (originalRows wrong)).HasType [Pair] L :=
    .cfg (family deadTy) (initial.renameLabels ren) blocks
  exact .case (.var rfl) (inner.renameVars ((Ren.wk [] (taggedPair D)).lift Pair)) (.br rfl (.var rfl))

private theorem exact_graph (wrong : Bool) (D deadTy : Ty Empty) : (graph wrong).HasType [] (boundary wrong) :=
  .cfg (slots (taggedPair D)) (.br rfl (.inl (.pair .unit .unit))) (fun _ => guardedRow_typed wrong D deadTy)

/-- Changing the second Unit exit to carry a pair is accepted at its own
typed boundary and rejected at the original ordered interface. -/
example : (graph true).HasType [] (boundary true) ∧
    NestedAdmission.Finite.compare? keep types (graph true) (boundary true) = .certified ∧
    NestedAdmission.Finite.compare? keep types (graph true) (boundary false) = .unknown :=
  ⟨exact_graph true U U, by decide, by decide⟩

/-- A missing exit is also rejected, even when all earlier exits match. -/
example : NestedAdmission.Finite.compare? keep types (graph false) [U, U] = .unknown := by decide

private def exitReplies (first : Fin 3) : Op → Value Empty → Unit → Value Empty → Unit → Prop
  | .unitRequest, .unit, (), result, () =>
      result = Fin.cases (.inr (.inl .unit))
        (Fin.cases (.inr (.inr .unit)) (fun _ => .inl (.pair .unit .unit))) first
  | .pairRequest, .pair .unit .unit, (), result, () => result = .inr (.pair .unit .unit)
  | _, _, _, _, _ => False

/-- The first two exits return the same Unit value at different ordinals. -/
example : Semantics.Region.Eval (exitReplies 0) (fun _ => .unit) (graph false) () 0 .unit () := by
  refine .cfg (.br (.inl (.pair .unit .unit))) ?_
  refine .step (label := 0) (next := 1) (by decide) ?_ (.exit (by decide))
  refine .case_inl .var (.cfg (.br .unit) ?_)
  exact .step (label := 0) (next := 4) (by decide)
    (.case_inr (.op .var rfl) (.case_inl .var (.br .var))) (.exit (by decide))

example : Semantics.Region.Eval (exitReplies 1) (fun _ => .unit) (graph false) () 1 .unit () := by
  refine .cfg (.br (.inl (.pair .unit .unit))) ?_
  refine .step (label := 0) (next := 2) (by decide) ?_ (.exit (by decide))
  refine .case_inl .var (.cfg (.br .unit) ?_)
  exact .step (label := 0) (next := 5) (by decide)
    (.case_inr (.op .var rfl) (.case_inr .var (.br .var))) (.exit (by decide))

/-- The third exit takes the second request and returns its pair reply. -/
example : Semantics.Region.Eval (exitReplies 2) (fun _ => .unit) (graph false) () 2 (.pair .unit .unit) () := by
  refine .cfg (.br (.inl (.pair .unit .unit))) ?_
  refine .step (label := 0) (next := 3) (by decide) ?_ (.exit (by decide))
  refine .case_inl .var (.cfg (.br .unit) ?_)
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := ()) (by decide)
    (.case_inl (.op .var rfl) (.br .var)) ?_
  exact .step (label := 2) (next := 6) (by decide)
    (.case_inr (.op .var rfl) (.br .var)) (.exit (by decide))

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M (boundary false))

/-- Independent witnesses use different outer right summands and dead
middle types. The checker compares their original three-exit arrows. -/
example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      RegionDenotes J M (exact_graph false U U) f ∧
      RegionDenotes J M (exact_graph false .empty .empty) g ∧ f = g := by
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (slots (taggedPair U))
    (.br rfl (.inl (.pair .unit .unit)) : start.HasType [] (outerLabels (taggedPair U) false))
    (fun _ => guardedRow_typed false U U)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (slots (taggedPair .empty))
    (.br rfl (.inl (.pair .unit .unit)) : start.HasType [] (outerLabels (taggedPair .empty) false))
    (fun _ => guardedRow_typed false .empty .empty)
  have dl : RegionDenotes J M (exact_graph false U U) f := left.denotes J M
  have dr : RegionDenotes J M (exact_graph false .empty .empty) g := right.denotes J M
  have ok : NestedAdmission.Finite.compare? keep types (graph false) (boundary false) = .certified := by decide
  exact ⟨f, g, dl, dr, NestedAdmission.Finite.compare?_sound J M roll ok dl dr⟩

end Model

namespace OuterMask

private def keepOuter : Fin 1 ↪ Fin 3 :=
  ⟨fun _ => 1, by intro i j _; exact Subsingleton.elim i j⟩

private def outerTypes (D omitted : Ty Empty) : Fin 3 → Ty Empty :=
  Fin.cases omitted (Fin.cases (taggedPair D) (fun _ => U))

private def fullEntry := start.renameLabels (retainLabelIndex keepOuter)

private def unusedRow : Region Op := (Region.br 1 .unit).renameLabels (retainLabelIndex keepOuter)

private def forbiddenInner : Region Op := .cfg (.br 3 .unit) 3 (fun _ => .br 6 .unit)

/-- The nested entry targets original outer slot zero, after skipping three
inner locals. Its retained outer sibling is at slot one. -/
private def forbiddenRow : Region Op :=
  .case (.var 0) (forbiddenInner.renameVars (Silmaril.DeBruijn.lift Nat.succ)) (.br 1 (.var 1))

private def fullRows (bad : Bool) : Fin 3 → Region Op :=
  Fin.cases unusedRow
    (Fin.cases (if bad then forbiddenRow else (guardedRow false).renameLabels (retainLabelIndex keepOuter))
      (fun _ => unusedRow))

private def fullGraph (bad : Bool) : Region Op := .cfg fullEntry 3 (fullRows bad)

private theorem fullEntry_typed (D omitted : Ty Empty) :
    fullEntry.HasType [] (List.ofFn (outerTypes D omitted) ++ boundary false) :=
  (show start.HasType [] (List.ofFn (fun i => outerTypes D omitted (keepOuter i)) ++ boundary false) from
    .br rfl (.inl (.pair .unit .unit))).renameLabels (retainLabelRen keepOuter _ _)

private theorem fullRows_typed (D omitted innerOmitted : Ty Empty) (i : Fin 3) :
    (fullRows false i).HasType [outerTypes D omitted i] (List.ofFn (outerTypes D omitted) ++ boundary false) := by
  let small := List.ofFn (fun j => outerTypes D omitted (keepOuter j)) ++ boundary false
  have er (A : Ty Empty) : (Region.br 1 .unit : Region Op).HasType [A] small := .br rfl .unit
  have ren := retainLabelRen keepOuter (outerTypes D omitted) (boundary false)
  exact Fin.cases ((er omitted).renameLabels ren)
    (Fin.cases ((guardedRow_typed false D innerOmitted).renameLabels ren)
      (fun _ => (er U).renameLabels ren)) i

private theorem rejected_typed : (fullGraph true).HasType [] (boundary false) := by
  refine .cfg (outerTypes U U) (fullEntry_typed U U) ?_
  intro i
  refine Fin.cases (fullRows_typed U U U 0)
    (Fin.cases ?_ (fun _ => fullRows_typed U U U 2)) i
  have inner : forbiddenInner.HasType [Pair] (List.ofFn (outerTypes U U) ++ boundary false) :=
    .cfg (fun _ => U) (.br rfl .unit) (fun _ => .br rfl .unit)
  exact .case (.var rfl) (inner.renameVars ((Ren.wk [] (taggedPair U)).lift Pair)) (.br rfl (.var rfl))

/-- The bad graph is exactly typed. Outer restriction itself fails when it
finds the nested entry's transfer into the omitted outer slot. -/
example : (fullGraph true).HasType [] (boundary false) ∧
    CfgRestriction.check? keepOuter (boundary false).length (fullGraph true) = none ∧
    NestedAdmission.Finite.Outer.compare? keepOuter keep types (fullGraph true) (boundary false) = .unknown :=
  ⟨rejected_typed, rfl, by decide⟩

/-- At runtime the nested entry really enters outer slot zero, whose row
takes the first actual exit. -/
example : Semantics.Region.Eval (exitReplies 0) (fun _ => .unit) (fullGraph true) () 0 .unit () := by
  refine .cfg (.br (.inl (.pair .unit .unit))) ?_
  refine .step (label := 1) (next := 0) (middle := .unit) (s₁ := ()) (by decide) ?_ ?_
  · exact .case_inl .var (.cfg (.br .unit) (.exit (by decide)))
  · exact .step (label := 0) (next := 3) (by decide) (.br .unit) (.exit (by decide))

/-- Both tables contribute local label offsets. The original full graph
still routes the pair reply to actual exit ordinal two. -/
example : Semantics.Region.Eval (exitReplies 2) (fun _ => .unit) (fullGraph false) () 2 (.pair .unit .unit) () := by
  refine .cfg (.br (.inl (.pair .unit .unit))) ?_
  refine .step (label := 1) (next := 5) (by decide) ?_ (.exit (by decide))
  refine .case_inl .var (.cfg (.br .unit) ?_)
  refine .step (label := 0) (next := 2) (middle := .pair .unit .unit) (s₁ := ()) (by decide)
    (.case_inl (.op .var rfl) (.br .var)) ?_
  exact .step (label := 2) (next := 8) (by decide)
    (.case_inr (.op .var rfl) (.br .var)) (.exit (by decide))

section Model

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel (Ty Empty) V) [InstructionModel J M Op]

local notation "Arrow" => J.obj (ctxObj M []) ⟶ J.obj (labelObj M (boundary false))

/-- The exact original witnesses use full outer and inner tables. Their
omitted outer types, omitted inner types and outer right summands differ. -/
example (roll : IterationRolling C) :
    ∃ f g : Arrow,
      CfgDenotesAt J M (outerTypes U U) fullEntry (fullRows false) f ∧
      CfgDenotesAt J M (outerTypes .empty .empty) fullEntry (fullRows false) g ∧ f = g := by
  obtain ⟨f, left⟩ := CfgDenotesAt.exists_of_typing J M (outerTypes U U)
    (fullEntry_typed U U) (fullRows_typed U U U)
  obtain ⟨g, right⟩ := CfgDenotesAt.exists_of_typing J M (outerTypes .empty .empty)
    (fullEntry_typed .empty .empty) (fullRows_typed .empty .empty .empty)
  have tl : (fullGraph false).HasType [] (boundary false) :=
    .cfg (outerTypes U U) (fullEntry_typed U U) (fullRows_typed U U U)
  have tr : (fullGraph false).HasType [] (boundary false) :=
    .cfg (outerTypes .empty .empty) (fullEntry_typed .empty .empty) (fullRows_typed .empty .empty .empty)
  have dl : RegionDenotes J M tl f := left.denotes J M
  have dr : RegionDenotes J M tr g := right.denotes J M
  have ok : NestedAdmission.Finite.Outer.compare? keepOuter keep types (fullGraph false) (boundary false) =
      .certified := by decide
  exact ⟨f, g, left, right, NestedAdmission.Finite.Outer.compare?_sound J M roll ok dl dr⟩

end Model

end OuterMask

end OrderedExits

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical.NestedCfgFiniteAdmissionExample
