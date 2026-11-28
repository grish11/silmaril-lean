module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Compile.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CompileTables

/-! # Every table of literal request trees has a router table

No seed is added. The expansion is an equation of default Paper. No
router table or layout is supplied from outside.

## The construction

`TreeTable.outlineAt` takes a request that stands directly at a reply of
a row, makes it a new state zero and leaves a jump with the same query in
its place. The other states keep their order behind it.

* `TreeTable.outline_inline`: writing the new state back inside recovers
  the table literally.
* `TreeTable.outline_arrow`: so the entered loops agree in default Paper,
  by #5244's `TreeTable.inlineFront_arrow`.
* `TreeTable.outline_asks`: one step removes exactly one inner request.
* `TreeTable.exists_router`: by induction on the number of inner
  requests, every tree table has a router table with the same entered
  loops, with a map of the old states into its states. Every program of
  the router table is a program of the tree table.

A request is moved before the requests inside it, and each new state is
put in front. So in the final table a parent has a larger index than its
children, and the old states are the last ones. That order is the reverse
of `Router.Forward`, which is not used: each step is undone by one
`inlineFront`, and the theorem follows from the steps directly. Each
occurrence of a request gets its own state; equal subtrees are not shared.

## Completeness for every source table

`LTable` is a table of trees of labelled requests.

* `LTable.exists_router`: a router table of labelled requests with equal
  entered loops, for every such table.
* `LTable.eqv_iff_valid`: two source tables are equal at given entries
  exactly when they are valid in every supported model.
* `LTable.eqv_iff_prefix`, `LTable.eqv_iff_bisimulation`: there are
  router tables for the two sources such that, at all entries, equality of
  the sources is equality of the request-prefix observations of the
  routers, and is the existence of a bisimulation between them.

## Regression

`sourceTable` is written as trees: two rows, the second request used at
three replies of row zero with two different queries, and a row that
never returns. `source_eqv_explicit`: it equals the hand-written table in
which the second request is one explicit state that three replies jump
to. `source_ne`: with another label on the row that never returns the
sources differ; the routers are separated by the pending first request.

## Not proved

* Sharing of equal subtrees, and that the map of old states is the
  iterated successor. Neither is needed for the statements above.
* Several requests inside one written row program. Those remain a single
  opaque step; they are not request trees and are not covered.
* Nothing is claimed about packed dispatchers in general.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K₁ K₂ : Nat}

/-! ## One step -/

section Step

variable (t : TreeTable K) (i : Fin (K + 1)) (x y q : Bool) (p : Program) (ks : Bool → Bool → Tree K)
  (h : t.kids i x y = .ask q p ks)

include h

theorem TreeTable.outline_inline : (t.outlineAt i x y q p ks).inlineFront = t :=
  Tables.outline_inline t i x y q p ks h

theorem TreeTable.outline_arrow (j : Fin (K + 1)) :
    ofRegion (t.entered_typed j) = ofRegion ((t.outlineAt i x y q p ks).entered_typed j.succ) :=
  Tables.outline_arrow t i x y q p ks h j

theorem TreeTable.outline_asks : (t.outlineAt i x y q p ks).asks + 1 = t.asks :=
  Tables.outline_asks t i x y q p ks h

end Step

/-! ## Every table -/

/-- Every tree table has a router table with the same entered loops, in
default Paper. -/
theorem TreeTable.exists_router (Q : Program → Prop) (t : TreeTable K) (hall : t.All Q) :
    ∃ (M : Nat) (R : Router M) (e : Fin (K + 1) → Fin (M + 1)), (∀ m, Q (R.prog m)) ∧
      ∀ j, ofRegion (t.entered_typed j) = ofRegion (R.entered_typed (e j)) :=
  Tables.exists_router Q t.asks t (Nat.le_refl _) hall

/-- Every table of labelled request trees has a router table of labelled
requests with equal entered loops. -/
theorem LTable.exists_router (t : LTable K) :
    ∃ (M : Nat) (label : Fin (M + 1) → Bool) (act : Fin (M + 1) → Bool → Bool → Act M)
      (e : Fin (K + 1) → Fin (M + 1)),
      ∀ j, Eqv false [State] (t.entered j) ((Router.ofLabels label act).entered (e j)) [Bit] :=
  Tables.ltable_eqv_router t

/-! ## Completeness -/

/-- Routers for the two sources whose request-prefix observations decide
equality of the sources at all entries. -/
theorem LTable.eqv_iff_prefix (t₁ : LTable K₁) (t₂ : LTable K₂) :
    ∃ (M₁ : Nat) (label₁ : Fin (M₁ + 1) → Bool) (act₁ : Fin (M₁ + 1) → Bool → Bool → Act M₁)
      (e₁ : Fin (K₁ + 1) → Fin (M₁ + 1)) (M₂ : Nat) (label₂ : Fin (M₂ + 1) → Bool)
      (act₂ : Fin (M₂ + 1) → Bool → Bool → Act M₂) (e₂ : Fin (K₂ + 1) → Fin (M₂ + 1)),
      ∀ i₁ i₂, Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] ↔
        (Router.ofLabels label₁ act₁).prefixObservations (e₁ i₁) false =
          (Router.ofLabels label₂ act₂).prefixObservations (e₂ i₂) false :=
  let ⟨M₁, label₁, act₁, e₁, E₁⟩ := t₁.exists_router
  let ⟨M₂, label₂, act₂, e₂, E₂⟩ := t₂.exists_router
  ⟨M₁, label₁, act₁, e₁, M₂, label₂, act₂, e₂, fun i₁ i₂ =>
    ⟨fun e => (Router.labels_eqv_iff_prefix label₁ act₁ label₂ act₂ _ _).1
        ((E₁ i₁).symm.trans (e.trans (E₂ i₂))),
      fun h => (E₁ i₁).trans (((Router.labels_eqv_iff_prefix label₁ act₁ label₂ act₂ _ _).2 h).trans
        (E₂ i₂).symm)⟩⟩

/-- Routers for the two sources whose bisimulations decide equality of the
sources at all entries. -/
theorem LTable.eqv_iff_bisimulation (t₁ : LTable K₁) (t₂ : LTable K₂) :
    ∃ (M₁ : Nat) (label₁ : Fin (M₁ + 1) → Bool) (act₁ : Fin (M₁ + 1) → Bool → Bool → Act M₁)
      (e₁ : Fin (K₁ + 1) → Fin (M₁ + 1)) (M₂ : Nat) (label₂ : Fin (M₂ + 1) → Bool)
      (act₂ : Fin (M₂ + 1) → Bool → Bool → Act M₂) (e₂ : Fin (K₂ + 1) → Fin (M₂ + 1)),
      ∀ i₁ i₂, Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] ↔
        ∃ R : Fin (M₁ + 1) → Fin (M₂ + 1) → Prop, (∀ x y, R x y → label₁ x = label₂ y) ∧
          (∀ x y, R x y → ∀ tag pl, Act.Rel R (act₁ x tag pl) (act₂ y tag pl)) ∧ R (e₁ i₁) (e₂ i₂) :=
  let ⟨M₁, label₁, act₁, e₁, E₁⟩ := t₁.exists_router
  let ⟨M₂, label₂, act₂, e₂, E₂⟩ := t₂.exists_router
  ⟨M₁, label₁, act₁, e₁, M₂, label₂, act₂, e₂, fun i₁ i₂ =>
    ⟨fun e => (Router.labels_eqv_iff label₁ act₁ label₂ act₂ _ _).1 ((E₁ i₁).symm.trans (e.trans (E₂ i₂))),
      fun h => (E₁ i₁).trans (((Router.labels_eqv_iff label₁ act₁ label₂ act₂ _ _).2 h).trans (E₂ i₂).symm)⟩⟩

/-- Two source tables are equal at given entries exactly when they are
valid in every supported model. -/
theorem LTable.eqv_iff_valid (t₁ : LTable K₁) (t₂ : LTable K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] ↔
      Valid (t₁.entered_typed i₁).hasType (t₂.entered_typed i₂).hasType :=
  let ⟨_, label₁, act₁, e₁, E₁⟩ := t₁.exists_router
  let ⟨_, label₂, act₂, e₂, E₂⟩ := t₂.exists_router
  ⟨fun e => valid_of_eqv false e _ _,
    fun v => (E₁ i₁).trans (((Router.labels_eqv_iff_valid' label₁ act₁ label₂ act₂ (e₁ i₁) (e₂ i₂)).2
      (Valid.trans (Valid.symm (valid_of_eqv false (E₁ i₁) _ _))
        (Valid.trans v (valid_of_eqv false (E₂ i₂) _ _)))).trans (E₂ i₂).symm)⟩

/-! ## Regression -/

/-- The written source equals the table with the second request as one
explicit state, at both entries. -/
theorem source_eqv_explicit (a o d : Bool) (i : Fin 2) :
    Eqv false [State] ((sourceTable a o d).entered i)
      ((Router.ofLabels (explicitLabel a o d) explicitAct).entered i.succ) [Bit] :=
  Tables.source_eqv_explicit a o d i

/-- With another label on the row that never returns the sources differ. -/
theorem source_ne (a o : Bool) {d d' : Bool} (ne : d ≠ d') :
    ¬ Eqv false [State] ((sourceTable a o d).entered 1) ((sourceTable a o d').entered 1) [Bit] :=
  fun e => ne (Router.prefix_label (explicitLabel a o d) explicitAct (explicitLabel a o d') explicitAct 2 2
    false false (Router.prefix_sound
      ((source_eqv_explicit a o d 1).symm.trans (e.trans (source_eqv_explicit a o d' 1))) false))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
