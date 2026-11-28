module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Entry.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Capture.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EntryRegression

/-! # Rows that keep their entry state, at the original entries

No seed is added. Nothing here is inferred from a model.

## Default Paper

These are equations of arrows of default Paper. They use no opt-in rule.

* `Router.matched_of_carries`: a router all of whose repeats carry the
  Bit `c` assigns to their target is `Matched c`.
* `resetRows_entered`: the reusable split-state lemma. If the rows are
  `Matched c`, the rows with their queries reset to `c`, entered at a
  state `x`, are the reset to `c x` followed by the rows entered at `x`.
  It is the roll law of iteration applied to the reset.
* `const_resetRegion`: the reset to `q` does nothing on the constant `q`.
* `state_eta`: a region on a state is the case on the state's Bit of the
  region entered with the two constants. It uses the native case on a
  variable and initiality of the empty summand.
* `caseEntry_pointed`: a case of two constant entries of literal request
  trees is those trees at each constant.

## The opt-in quotient: the split encoding

* `entrySplit_eqv_entryRouter`: loop preservation for the encoding. The
  split table entered at a split state of row `j` is the original table
  entered at `j`, for every state. This is the existing router-morphism
  fold of the opt-in quotient, which rests on the phase-uniformity seed.
  Whether it holds in default Paper is not decided here.
* `entryRouter_pointed`: the original table entered with the constant `q`
  at row `j` is `entrySource` entered with `q` at `splitIdx j q`. The
  proof resets both split tables, compares their rows on the constant
  with `entryProgram_ask_eqv` (unit η), and removes the resets with
  `resetRows_entered`.
* `entryRouter_eqv_entryCase`: the two constant entries recombined. The
  original table entered at `j`, on an arbitrary state, is the split
  table of literal request trees entered by a case on that state.

## The opt-in quotient: completeness

* `Pointed.eqv_iff_sources`: two loops that are literal sources at each
  constant are equal exactly when their sources are equal at each
  constant.
* `Pointed.complete`: exactly when they are valid in every supported
  model. The converse reads the request-prefix model at each constant:
  for literal request trees the observations at one constant entry
  determine the entered loop.
* `entryRouter_complete`, `entryRouter_eqv_capRouter_iff_valid`,
  `entryRouter_eqv_ltable_iff_valid`: the instances for tables of
  `entryProgram` rows at their original entries, against one another,
  against tables of `capProgram` rows, and against literal request trees.

These depend on the phase-uniformity quotient, unit η and the
request-prefix model. They are not statements about default Paper.

## Regression

The one-row table of `turnAct` returns the Bit it is given, or repeats
with the negated Bit, so a repeat changes the entry state.

* `entryRouter_ne_capRouter`: keeping the entry state differs from
  keeping the first reply's payload.
* `entryRouter_ne_frozen`: after a repeat the kept Bit is the Bit the
  repeat carried. The table differs from the frozen split table, whose
  repeats stay in their copy and so keep the first state for ever. The
  two agree until a repeat; the proof separates them after one.

## Scope

The rows are `entryProgram`. Rows that read both their entry state and
earlier replies are treated in `Composite.Environment`. No statement is
made here for the whole grammar of written programs or for packed
dispatchers in general.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

open CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (sumIso)

variable {K K₁ K₂ : Nat}

/-! ## Default Paper -/

/-- A router all of whose repeats carry the Bit of their target is matched. -/
theorem Router.matched_of_carries {M : Nat} (c : Fin (M + 1) → Bool) (t : Router M)
    (hc : ∀ x a b, (t.act x a b).Carries c) : Matched c t.rows_typed :=
  Tables.router_matched c t hc

/-- Matched rows with their queries reset, entered at a state, are the
reset followed by the rows entered at that state. In default Paper. -/
theorem resetRows_entered {M : Nat} (c : Fin (M + 1) → Bool) {rows : Fin (M + 1) → Region signature.Instr}
    (h : ∀ x, ValueBranches [State] (rows x) [Silmaril.coprod Bit (States M)]) (m : Matched c h)
    (x : Fin (M + 1)) :
    ofRegion (dispatchEntered_typed (resetRows_typed c h) x) =
      ofRegion (reset_typed (c x)) ≫ ofRegion (dispatchEntered_typed h x) :=
  Tables.reset_entered c h m x

/-- The reset to `q` does nothing on the constant `q`. -/
theorem const_resetRegion (q : Bool) :
    ofRegion (const_typed q) ≫ ofRegion (reset_typed q) = ofRegion (const_typed q) :=
  Tables.const_reset q

/-- A region on a state is the case on the state's Bit of the region
entered with the two constants, in default Paper. -/
theorem state_eta {r : Region signature.Instr} (h : ValueBranches [State] r [Bit]) :
    ofRegion h = ofRegion (caseEntry_typed (constEntry_typed false h) (constEntry_typed true h)) :=
  Tables.state_eta h

/-- A case of two constant entries of literal request trees is those
trees at each constant. The equations are of default Paper. -/
theorem caseEntry_pointed (t : Bool → LTable K) (x : Bool → Fin (K + 1)) :
    Pointed (caseEntry (constEntry false ((t false).entered (x false)))
      (constEntry true ((t true).entered (x true)))) t x :=
  Tables.case_pointed t x

/-! ## The opt-in quotient: the split encoding -/

section Split

variable (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)

/-- The split table entered at a split state of row `j` is the original
table entered at `j`. -/
theorem entrySplit_eqv_entryRouter (j : Fin (K + 1)) (q : Bool) :
    Eqv false [State] ((entrySplit l₁ l₂ act).entered (splitIdx j q)) ((entryRouter l₁ l₂ act).entered j)
      [Bit] :=
  Tables.split_fold l₁ l₂ act j q

/-- The original table entered with each constant is the split table of
literal request trees entered with that constant. -/
theorem entryRouter_pointed (j : Fin (K + 1)) :
    Pointed ((entryRouter l₁ l₂ act).entered j) (fun _ => entrySource l₁ l₂ act) (splitIdx j) :=
  Tables.entry_pointed l₁ l₂ act j

/-- The original table, on an arbitrary state, is the split table of
literal request trees entered by a case on that state. -/
theorem entryRouter_eqv_entryCase (j : Fin (K + 1)) :
    Eqv false [State] ((entryRouter l₁ l₂ act).entered j) (entryCase l₁ l₂ act j) [Bit] :=
  Tables.entry_case_eqv l₁ l₂ act j

end Split

/-- A loop equal to a table of literal request trees is that table at
each constant. -/
theorem LTable.pointed_of_eqv {r : Region signature.Instr} (h : ValueBranches [State] r [Bit]) (t : LTable K)
    (x : Fin (K + 1)) (e : Eqv false [State] r (t.entered x) [Bit]) : Pointed r (fun _ => t) (fun _ => x) :=
  Tables.pointed_of_eqv h t x e

/-! ## The opt-in quotient: completeness -/

section Complete

variable {r r' : Region signature.Instr} {t : Bool → LTable K₁} {x : Bool → Fin (K₁ + 1)}
  {t' : Bool → LTable K₂} {x' : Bool → Fin (K₂ + 1)}

/-- Loops that are literal sources at each constant are equal exactly
when their sources are equal at each constant. -/
theorem Pointed.eqv_iff_sources (hp : Pointed r t x) (hp' : Pointed r' t' x')
    (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit]) :
    Eqv false [State] r r' [Bit] ↔
      ∀ q, Eqv false [State] ((t q).entered (x q)) ((t' q).entered (x' q)) [Bit] :=
  Tables.pointed_iff_sources h h' hp hp'

/-- And exactly when they are valid in every supported model. -/
theorem Pointed.complete (hp : Pointed r t x) (hp' : Pointed r' t' x')
    (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit]) :
    Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  Tables.pointed_complete h h' hp hp'

end Complete

/-- Two tables of rows that keep their entry state are equal at given
original entries exactly when they are valid in every supported model. -/
theorem entryRouter_complete (l₁ l₂ : Fin (K₁ + 1) → Bool) (act : Fin (K₁ + 1) → Bool → Bool → Act K₁)
    (m₁ m₂ : Fin (K₂ + 1) → Bool) (act' : Fin (K₂ + 1) → Bool → Bool → Act K₂) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((entryRouter l₁ l₂ act).entered i₁) ((entryRouter m₁ m₂ act').entered i₂) [Bit] ↔
      Valid ((entryRouter l₁ l₂ act).entered_typed i₁).hasType
        ((entryRouter m₁ m₂ act').entered_typed i₂).hasType :=
  (entryRouter_pointed l₁ l₂ act i₁).complete (entryRouter_pointed m₁ m₂ act' i₂)
    ((entryRouter l₁ l₂ act).entered_typed i₁) ((entryRouter m₁ m₂ act').entered_typed i₂)

/-- The same against a table of rows that keep their first reply. -/
theorem entryRouter_eqv_capRouter_iff_valid (l₁ l₂ : Fin (K₁ + 1) → Bool)
    (act : Fin (K₁ + 1) → Bool → Bool → Act K₁) (m₁ m₂ : Fin (K₂ + 1) → Bool)
    (act' : Fin (K₂ + 1) → Bool → Bool → Act K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((entryRouter l₁ l₂ act).entered i₁) ((capRouter m₁ m₂ act').entered i₂) [Bit] ↔
      Valid ((entryRouter l₁ l₂ act).entered_typed i₁).hasType
        ((capRouter m₁ m₂ act').entered_typed i₂).hasType :=
  (entryRouter_pointed l₁ l₂ act i₁).complete
    (LTable.pointed_of_eqv ((capRouter m₁ m₂ act').entered_typed i₂) (capSource m₁ m₂ act') i₂
      (capRouter_eqv_capSource m₁ m₂ act' i₂))
    ((entryRouter l₁ l₂ act).entered_typed i₁) ((capRouter m₁ m₂ act').entered_typed i₂)

/-- The same against any table of literal request trees. -/
theorem entryRouter_eqv_ltable_iff_valid (l₁ l₂ : Fin (K₁ + 1) → Bool)
    (act : Fin (K₁ + 1) → Bool → Bool → Act K₁) (s : LTable K₂) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((entryRouter l₁ l₂ act).entered i₁) (s.entered i₂) [Bit] ↔
      Valid ((entryRouter l₁ l₂ act).entered_typed i₁).hasType (s.entered_typed i₂).hasType :=
  (entryRouter_pointed l₁ l₂ act i₁).complete
    (LTable.pointed_of_eqv (s.entered_typed i₂) s i₂ (Paper.Extension.Eqv.refl (s.entered_typed i₂).hasType))
    ((entryRouter l₁ l₂ act).entered_typed i₁) (s.entered_typed i₂)

/-! ## Regression -/

/-- The split table of the one-row table of `turnAct` is the written
table `turnSource false`. -/
theorem entrySource_turn (l₁ l₂ : Bool) :
    entrySource (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct = turnSource false l₁ l₂ :=
  Tables.turn_source l₁ l₂

/-- Keeping the entry state is not keeping the first reply's payload. -/
theorem entryRouter_ne_capRouter (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((entryRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered 0)
      ((capRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered 0) [Bit] :=
  Tables.entry_ne_cap l₁ l₂

/-- After a repeat the kept Bit is the Bit the repeat carried, not the
first state. -/
theorem entryRouter_ne_frozen (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((entryRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered 0)
      (frozenCase l₁ l₂) [Bit] :=
  Tables.entry_ne_frozen l₁ l₂

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
