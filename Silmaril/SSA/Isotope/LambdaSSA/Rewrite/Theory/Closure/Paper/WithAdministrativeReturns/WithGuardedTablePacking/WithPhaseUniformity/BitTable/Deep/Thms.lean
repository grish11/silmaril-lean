module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Deep.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Prefix.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Outline.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.DeepTables

/-! # Two-request rows: expansion to router states, and completeness

No seed is added. The expansion is an equation of default Paper.

## The rows

A deep row sends one labelled request. Each of its four replies either
takes a plain action, or continues at once with a second labelled
request, sent with a chosen query, whose four replies take plain
actions. So a round has one or two requests; whether the second is sent,
and with which query, depends on the first reply. A table has one
continuation, which may be inlined at any reply of any row.

## Expansion

* `iterate_outline` (default Paper): a row run in place of the jumps to a
  new state gives the loop of the table with that state, entered at an old
  state. It follows from rolling, the fixpoint law and the codiagonal law.
* `dispatch_outline_arrow`: the same for literal dispatchers of any rows,
  with state zero as the new state.
* `Deep.expand_arrow`, `Deep.expand_eqv`: a deep table entered at state
  `i` equals its expansion entered at `i + 1`, for arbitrary row programs.
  The expansion is the router table with the continuation as state zero
  and a jump to it at each inlined occurrence. Effect order, queries and
  final returns are those of the literal regions; nothing is normalized.

## Completeness

For deep tables of labelled requests and any entries, the entered loops
are equal exactly when a bisimulation relates their expansions
(`Deep.labels_eqv_iff`), exactly when they are valid in every supported
model (`Deep.labels_eqv_iff_valid`). `Deep.labels_eqv_router_iff` compares
a deep table with a router table of explicit rows. These are #5210 through
the expansion; no liveness is assumed.

## Regression

* `duo_eqv_split`: one state whose second request is sent after two of
  the four replies, with the reply payload as its query, against explicit
  rows with other boundaries: three states, the second request having one
  state for each query.
* `duo_ne_split`: with another label on the explicit second request the
  tables differ.
* `loop_ne`: two deep rows that never return and differ in the label of
  the second request are not equal.

## Not proved

* More than one continuation, or more than two requests in a round, are
  not handled here. Finitely many continuations and request trees of any
  depth are in `BitTable/Nest/Thms.lean`.
* A second request inside a single written program, as opposed to a
  literal second row. Relating the two needs the step of a two-request
  program as a composite of one-request steps, which is not derived.
* Nothing is claimed about packed dispatchers in general.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion sumIso sumDesc sumInr)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K₁ K₂ : Nat}

/-! ## Expansion -/

/-- Outlining state zero of a literal dispatcher, in default Paper. -/
theorem dispatch_outline_arrow {rows : Fin (K + 1) → Region signature.Instr}
    {rows' : Fin (K + 2) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)])
    (h' : ∀ i, ValueBranches [State] (rows' i) [Silmaril.coprod Bit (States (K + 1))])
    (r₀ : ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K))
    (front : ofRegion (h' 0) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom =
      r₀ ≫ coprod.map (𝟙 _) (sumInr State (States K)))
    (row : ∀ i, (ofRegion (h' i.succ) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
        coprod.desc coprod.inl (sumDesc r₀ coprod.inr) =
      ofRegion (h i) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) (i : Fin (K + 1)) :
    ofRegion (dispatchEntered_typed h i) = ofRegion (dispatchEntered_typed h' i.succ) :=
  Tables.dispatch_outline h h' r₀ front row i

/-- A deep table and its expansion have the same entered loops, as arrows
of default Paper. -/
theorem Deep.expand_arrow (t : Deep K) (i : Fin (K + 1)) :
    ofRegion (t.entered_typed i) = ofRegion (t.expand.entered_typed i.succ) :=
  Tables.deep_expand_arrow t i

/-- Hence they are equal in the quotient. -/
theorem Deep.expand_eqv (t : Deep K) (i : Fin (K + 1)) :
    Eqv false [State] (t.entered i) (t.expand.entered i.succ) [Bit] :=
  Tables.deep_expand_eqv t i

/-- The expansion of a deep table of labelled requests. -/
theorem Deep.expand_ofLabels (label : Fin (K + 1) → Bool) (leaf : Fin (K + 1) → Bool → Bool → Leaf K)
    (lc : Bool) (ac : Bool → Bool → Act K) :
    (Deep.ofLabels label leaf lc ac).expand = Router.ofLabels (deepLabel label lc) (deepAct leaf ac) :=
  Tables.expand_ofLabels label leaf lc ac

theorem Deep.labels_expand_eqv (label : Fin (K + 1) → Bool) (leaf : Fin (K + 1) → Bool → Bool → Leaf K)
    (lc : Bool) (ac : Bool → Bool → Act K) (i : Fin (K + 1)) :
    Eqv false [State] ((Deep.ofLabels label leaf lc ac).entered i)
      ((Router.ofLabels (deepLabel label lc) (deepAct leaf ac)).entered i.succ) [Bit] :=
  Tables.deep_labels_eqv label leaf lc ac i

/-! ## Completeness -/

section Labels

variable (label₁ : Fin (K₁ + 1) → Bool) (leaf₁ : Fin (K₁ + 1) → Bool → Bool → Leaf K₁) (lc₁ : Bool)
  (ac₁ : Bool → Bool → Act K₁) (i₁ : Fin (K₁ + 1))

/-- A deep table against explicit router rows: equal exactly when a
bisimulation relates the expansion to the router table. -/
theorem Deep.labels_eqv_router_iff (label₂ : Fin (K₂ + 1) → Bool) (act₂ : Fin (K₂ + 1) → Bool → Bool → Act K₂)
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((Deep.ofLabels label₁ leaf₁ lc₁ ac₁).entered i₁)
        ((Router.ofLabels label₂ act₂).entered i₂) [Bit] ↔
      ∃ R : Fin (K₁ + 2) → Fin (K₂ + 1) → Prop, (∀ x y, R x y → deepLabel label₁ lc₁ x = label₂ y) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (deepAct leaf₁ ac₁ x tag pl) (act₂ y tag pl)) ∧ R i₁.succ i₂ :=
  ⟨fun e => (Router.labels_eqv_iff (deepLabel label₁ lc₁) (deepAct leaf₁ ac₁) label₂ act₂ i₁.succ i₂).1
      ((Deep.labels_expand_eqv label₁ leaf₁ lc₁ ac₁ i₁).symm.trans e),
    fun h => (Deep.labels_expand_eqv label₁ leaf₁ lc₁ ac₁ i₁).trans
      ((Router.labels_eqv_iff (deepLabel label₁ lc₁) (deepAct leaf₁ ac₁) label₂ act₂ i₁.succ i₂).2 h)⟩

variable (label₂ : Fin (K₂ + 1) → Bool) (leaf₂ : Fin (K₂ + 1) → Bool → Bool → Leaf K₂) (lc₂ : Bool)
  (ac₂ : Bool → Bool → Act K₂) (i₂ : Fin (K₂ + 1))

/-- Two deep tables: equal exactly when a bisimulation relates their
expansions. -/
theorem Deep.labels_eqv_iff :
    Eqv false [State] ((Deep.ofLabels label₁ leaf₁ lc₁ ac₁).entered i₁)
        ((Deep.ofLabels label₂ leaf₂ lc₂ ac₂).entered i₂) [Bit] ↔
      ∃ R : Fin (K₁ + 2) → Fin (K₂ + 2) → Prop,
        (∀ x y, R x y → deepLabel label₁ lc₁ x = deepLabel label₂ lc₂ y) ∧
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (deepAct leaf₁ ac₁ x tag pl) (deepAct leaf₂ ac₂ y tag pl)) ∧
        R i₁.succ i₂.succ :=
  ⟨fun e => (Deep.labels_eqv_router_iff label₁ leaf₁ lc₁ ac₁ i₁ _ _ i₂.succ).1
      (e.trans (Deep.labels_expand_eqv label₂ leaf₂ lc₂ ac₂ i₂)),
    fun h => ((Deep.labels_eqv_router_iff label₁ leaf₁ lc₁ ac₁ i₁ _ _ i₂.succ).2 h).trans
      (Deep.labels_expand_eqv label₂ leaf₂ lc₂ ac₂ i₂).symm⟩

/-- Exactly when they are valid in every supported model. -/
theorem Deep.labels_eqv_iff_valid :
    Eqv false [State] ((Deep.ofLabels label₁ leaf₁ lc₁ ac₁).entered i₁)
        ((Deep.ofLabels label₂ leaf₂ lc₂ ac₂).entered i₂) [Bit] ↔
      Valid ((Deep.ofLabels label₁ leaf₁ lc₁ ac₁).entered_typed i₁).hasType
        ((Deep.ofLabels label₂ leaf₂ lc₂ ac₂).entered_typed i₂).hasType :=
  ⟨fun e => valid_of_eqv false e _ _,
    fun v => (Deep.labels_expand_eqv label₁ leaf₁ lc₁ ac₁ i₁).trans
      (((Router.labels_eqv_iff_valid' _ _ _ _ i₁.succ i₂.succ).2
        (Valid.trans (Valid.symm (valid_of_eqv false (Deep.labels_expand_eqv label₁ leaf₁ lc₁ ac₁ i₁) _ _))
          (Valid.trans v (valid_of_eqv false (Deep.labels_expand_eqv label₂ leaf₂ lc₂ ac₂ i₂) _ _)))).trans
        (Deep.labels_expand_eqv label₂ leaf₂ lc₂ ac₂ i₂).symm)⟩

end Labels

/-! ## Regression -/

/-- The two-request row equals the explicit rows with other boundaries. -/
theorem duo_eqv_split (a c : Bool) :
    Eqv false [State] ((Deep.ofLabels (fun _ => a) duoLeaf c duoCont).entered 0)
      ((Router.ofLabels (splitLabel a c) splitAct).entered 0) [Bit] :=
  (Deep.labels_eqv_router_iff (fun _ => a) duoLeaf c duoCont 0 (splitLabel a c) splitAct 0).2
    ⟨Tables.duoSplit, Tables.duoSplit_label a c, Tables.duoSplit_act, .inl ⟨rfl, rfl⟩⟩

/-- With another label on the explicit second request they differ. -/
theorem duo_ne_split (a : Bool) {c c' : Bool} (ne : c ≠ c') :
    ¬ Eqv false [State] ((Deep.ofLabels (fun _ => a) duoLeaf c duoCont).entered 0)
      ((Router.ofLabels (splitLabel a c') splitAct).entered 0) [Bit] := by
  intro e
  obtain ⟨R, hl, ha, r⟩ :=
    (Deep.labels_eqv_router_iff (fun _ => a) duoLeaf c duoCont 0 (splitLabel a c') splitAct 0).1 e
  exact ne (hl 0 1 (ha _ _ r false true).2)

/-- Two deep rows that never return and differ in the label of the second
request are not equal. -/
theorem loop_ne (a : Bool) {c c' : Bool} (ne : c ≠ c') :
    ¬ Eqv false [State] ((Deep.ofLabels (fun _ => a) loopLeaf c loopCont).entered 0)
      ((Deep.ofLabels (fun _ => a) loopLeaf c' loopCont).entered 0) [Bit] := by
  intro e
  obtain ⟨R, hl, ha, r⟩ :=
    (Deep.labels_eqv_iff (fun _ => a) loopLeaf c loopCont 0 (fun _ => a) loopLeaf c' loopCont 0).1 e
  exact ne (hl 0 0 (ha _ _ r false false).2)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
