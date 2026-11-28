module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Deep.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.NestTables

/-! # Literal request trees as cyclic rows: expansion and completeness

No seed is added. The expansion is an equation of default Paper.

## The source syntax

A row of a tree table is a first request with a `Tree` at each of its
four replies. A tree is a plain action (return a Bit, or jump to a state
with a query) or a further request, sent at once with a chosen query,
with a tree at each of its replies. The region is the literal nesting:
each inner request is written inside the reply branch that sends it, so a
round may have any finite number of requests along each path, and the
requests that follow depend on all earlier replies.

## The compiler

The target of a tree is a router table that has one state for each inner
request. `TreeTable.nest n` is the translation read from the target: it
writes the first `n` states of a table inside the rows that jump to them.
`Router.Forward n` is the layout assumption on the target: its first `n`
rows only jump to later states, a topological order of the inner requests.

* `TreeTable.inlineFront_arrow`: one state. This is the outlining law
  `iterate_outline` for tree rows.
* `TreeTable.nest_arrow`, `Router.nest_arrow`, `Router.nest_eqv`: any
  number of states, by induction on `n`. The table of literal trees
  entered at state `i` equals the router table entered at `shiftN n i`,
  as arrows of default Paper, for arbitrary row programs.

Several jumps to one inner state give several copies of its tree, so a
shared continuation is written out once per use.

## Completeness

`Router.nest_labels_eqv_iff`, `Router.nest_labels_eqv_iff_prefix`: for
nested tables of labelled requests and any entries, the entered loops are
equal exactly when a bisimulation relates their router tables, exactly
when those have the same observations in the request-prefix model. These
are #5210 through the expansion; no liveness is assumed.

## Regression

* `chained_nest_eqv`: three inner requests `A`, `B`, `C` and one state.
  One reply sends `A` with the reply's payload as query, another sends
  `B`; `A` sends `B`, `B` sends `C`. The tree at the first of these
  replies has depth three, so a round has up to four requests
  (`chained_depth`), and the tree at the other has depth two
  (`chained_depth_other`).
* `chained_boundaries`: all three written inside against only `A` written
  inside, with `B` and `C` as explicit states.
* `spiral_ne`: two nested rows that never return and differ in the label
  of the innermost request are not equal. The distinguishing prefix of
  their router tables has two completed exchanges (`spiral_prefix`,
  `spiral_prefix_not`).

## Not proved

* The theorem here starts from the router table with its inner states in
  topological order. A router table for every tree table is constructed
  in `BitTable/Nest/Compile/Thms.lean`.
* Several requests inside one written row program. Those are a single
  opaque step here: a tree's requests are separate literal rows. Relating
  the two needs the step of a multi-request program as a composite of
  one-request steps, which is not derived, and no composition equation for
  them is packaged.
* Nothing is claimed about packed dispatchers in general.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K₁ K₂ : Nat}

/-! ## Expansion -/

/-- A router table read as a tree table has the same regions. -/
theorem Router.toTrees_entered (t : Router K) (i : Fin (K + 1)) : t.toTrees.entered i = t.entered i :=
  rfl

/-- Writing state zero inside the rows that jump to it, in default Paper. -/
theorem TreeTable.inlineFront_arrow (t : TreeTable (K + 1)) (fwd : ∀ x y, (t.kids 0 x y).Above 0)
    (i : Fin (K + 1)) : ofRegion (t.inlineFront.entered_typed i) = ofRegion (t.entered_typed i.succ) :=
  Tables.inlineFront_arrow t fwd i

/-- Writing the first `n` states inside the rows that jump to them, in
default Paper. -/
theorem TreeTable.nest_arrow (n : Nat) (t : TreeTable (K + n))
    (fwd : ∀ k : Fin (K + n + 1), k.val < n → ∀ x y, (t.kids k x y).Above k.val) (i : Fin (K + 1)) :
    ofRegion ((TreeTable.nest n t).entered_typed i) = ofRegion (t.entered_typed (shiftN n i)) :=
  Tables.nest_arrow n t fwd i

/-- The literal request trees of a router table whose first `n` rows only
jump forward have the same entered loops as the router table. -/
theorem Router.nest_arrow (n : Nat) (t : Router (K + n)) (fwd : t.Forward n) (i : Fin (K + 1)) :
    ofRegion ((TreeTable.nest n t.toTrees).entered_typed i) = ofRegion (t.entered_typed (shiftN n i)) :=
  Tables.router_nest_arrow n t fwd i

theorem Router.nest_eqv (n : Nat) (t : Router (K + n)) (fwd : t.Forward n) (i : Fin (K + 1)) :
    Eqv false [State] ((TreeTable.nest n t.toTrees).entered i) (t.entered (shiftN n i)) [Bit] :=
  Tables.router_nest_eqv n t fwd i

/-! ## Completeness -/

section Labels

variable (n₁ n₂ : Nat) (label₁ : Fin (K₁ + n₁ + 1) → Bool) (act₁ : Fin (K₁ + n₁ + 1) → Bool → Bool → Act (K₁ + n₁))
  (label₂ : Fin (K₂ + n₂ + 1) → Bool) (act₂ : Fin (K₂ + n₂ + 1) → Bool → Bool → Act (K₂ + n₂))
  (fwd₁ : (Router.ofLabels label₁ act₁).Forward n₁) (fwd₂ : (Router.ofLabels label₂ act₂).Forward n₂)
  (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))

include fwd₁ fwd₂

/-- Two nested tables are equal exactly when a bisimulation relates their
router tables. -/
theorem Router.nest_labels_eqv_iff :
    Eqv false [State] ((TreeTable.nest n₁ (Router.ofLabels label₁ act₁).toTrees).entered i₁)
        ((TreeTable.nest n₂ (Router.ofLabels label₂ act₂).toTrees).entered i₂) [Bit] ↔
      ∃ R : Fin (K₁ + n₁ + 1) → Fin (K₂ + n₂ + 1) → Prop, (∀ x y, R x y → label₁ x = label₂ y) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (act₁ x tag pl) (act₂ y tag pl)) ∧
        R (shiftN n₁ i₁) (shiftN n₂ i₂) :=
  ⟨fun e => (Router.labels_eqv_iff label₁ act₁ label₂ act₂ _ _).1
      (((Router.nest_eqv n₁ _ fwd₁ i₁).symm.trans e).trans (Router.nest_eqv n₂ _ fwd₂ i₂)),
    fun h => (Router.nest_eqv n₁ _ fwd₁ i₁).trans
      (((Router.labels_eqv_iff label₁ act₁ label₂ act₂ _ _).2 h).trans (Router.nest_eqv n₂ _ fwd₂ i₂).symm)⟩

/-- Exactly when their router tables have the same observations in the
request-prefix model. -/
theorem Router.nest_labels_eqv_iff_prefix :
    Eqv false [State] ((TreeTable.nest n₁ (Router.ofLabels label₁ act₁).toTrees).entered i₁)
        ((TreeTable.nest n₂ (Router.ofLabels label₂ act₂).toTrees).entered i₂) [Bit] ↔
      (Router.ofLabels label₁ act₁).prefixObservations (shiftN n₁ i₁) false =
        (Router.ofLabels label₂ act₂).prefixObservations (shiftN n₂ i₂) false :=
  ⟨fun e => (Router.labels_eqv_iff_prefix label₁ act₁ label₂ act₂ _ _).1
      (((Router.nest_eqv n₁ _ fwd₁ i₁).symm.trans e).trans (Router.nest_eqv n₂ _ fwd₂ i₂)),
    fun h => (Router.nest_eqv n₁ _ fwd₁ i₁).trans
      (((Router.labels_eqv_iff_prefix label₁ act₁ label₂ act₂ _ _).2 h).trans
        (Router.nest_eqv n₂ _ fwd₂ i₂).symm)⟩

end Labels

/-! ## Regression -/

/-- The row with `A`, `B` and `C` written inside equals the four-state
router table. -/
theorem chained_nest_eqv (a b c o : Bool) :
    Eqv false [State]
      ((TreeTable.nest (K := 0) 3 (Router.ofLabels (chainedLabel a b c o) chainedAct).toTrees).entered 0)
      ((Router.ofLabels (chainedLabel a b c o) chainedAct).entered 3) [Bit] :=
  Router.nest_eqv (K := 0) 3 _ (Tables.chained_forward a b c o 3 (Nat.le_refl 3)) 0

/-- The reply that sends `A` is followed by up to three further requests. -/
theorem chained_depth (a b c o : Bool) :
    ((TreeTable.nest (K := 0) 3 (Router.ofLabels (chainedLabel a b c o) chainedAct).toTrees).kids 0
      false true).depth = 3 := by
  cases a <;> cases b <;> cases c <;> cases o <;> decide +kernel

/-- The reply that sends `B` is followed by up to two. -/
theorem chained_depth_other (a b c o : Bool) :
    ((TreeTable.nest (K := 0) 3 (Router.ofLabels (chainedLabel a b c o) chainedAct).toTrees).kids 0
      true false).depth = 2 := by
  cases a <;> cases b <;> cases c <;> cases o <;> decide +kernel

/-- All three written inside against only `A` written inside. -/
theorem chained_boundaries (a b c o : Bool) :
    Eqv false [State]
      ((TreeTable.nest (K := 0) 3 (Router.ofLabels (chainedLabel a b c o) chainedAct).toTrees).entered 0)
      ((TreeTable.nest (K := 2) 1 (Router.ofLabels (chainedLabel a b c o) chainedAct).toTrees).entered 2)
      [Bit] :=
  (chained_nest_eqv a b c o).trans
    (Router.nest_eqv (K := 2) 1 _ (Tables.chained_forward a b c o 1 (by decide)) 2).symm

/-- After two completed exchanges of the spiral the request of `B` is
pending. -/
theorem spiral_prefix (a b o g : Bool) :
    (Except.error b, FreeMonoid.of (event o g (false, false)) *
      (FreeMonoid.of (event a false (false, false)) * 1)) ∈
      (Router.ofLabels (spiralLabel a b o) spiralAct).prefixObservations 2 g :=
  Tables.spiral_prefix a b o g

/-- With another label on `B` there is no such prefix. -/
theorem spiral_prefix_not (a o g : Bool) {b b' : Bool} (ne : b ≠ b') :
    (Except.error b, FreeMonoid.of (event o g (false, false)) *
      (FreeMonoid.of (event a false (false, false)) * 1)) ∉
      (Router.ofLabels (spiralLabel a b' o) spiralAct).prefixObservations 2 g :=
  Tables.spiral_prefix_not a o g ne

/-- Two nested rows that never return and differ in the label of the
innermost request are not equal. -/
theorem spiral_ne (a o : Bool) {b b' : Bool} (ne : b ≠ b') :
    ¬ Eqv false [State]
      ((TreeTable.nest (K := 0) 2 (Router.ofLabels (spiralLabel a b o) spiralAct).toTrees).entered 0)
      ((TreeTable.nest (K := 0) 2 (Router.ofLabels (spiralLabel a b' o) spiralAct).toTrees).entered 0)
      [Bit] := by
  intro e
  have obs := (Router.nest_labels_eqv_iff_prefix (K₁ := 0) (K₂ := 0) 2 2 (spiralLabel a b o) spiralAct
    (spiralLabel a b' o) spiralAct (Tables.spiral_forward a b o) (Tables.spiral_forward a b' o) 0 0).1 e
  exact spiral_prefix_not a o false ne ((Set.ext_iff.1 obs _).1 (spiral_prefix a b o false))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
