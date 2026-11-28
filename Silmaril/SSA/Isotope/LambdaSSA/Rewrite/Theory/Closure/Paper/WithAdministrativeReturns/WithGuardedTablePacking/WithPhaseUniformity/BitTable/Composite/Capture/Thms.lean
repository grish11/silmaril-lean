module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Capture.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CaptureTables

/-! # A written row that keeps a Bit across its second request

No seed is added. Nothing here is inferred from a model. The factoring is
an equation of default Paper. Everything after it uses unit η, which is a
seed the opt-in quotient already contains. Default Paper is checked not
to prove unit η over the signature with no instructions
(`BoundSimulation.Obstruction.unit_eta_fails`). For the signature used
here that is neither derived nor refuted in this file.

## The written programs

`capProgram_written`, `capSecond_written` and `entryProgram_written` give
the literal regions. The kept Bit is a variable bound outside the second
request and used under it.

## Default Paper: the factoring

* `capProgram_step_arrow`: the written step of `capProgram l₁ l₂` is the
  step of its first request chained into `capSecond l₂`. The kept Bit is
  the state of the second step. It is its query, and its left reply
  returns it.
* `capRouter_arrow_carried`: so the table whose rows are these programs
  and the table `capCarried`, whose trees send `capSecond` with the kept
  Bit as a constant query, have the same entered loops at every entry.

These two use no opt-in rule. They do not make the second step a
labelled request: after its left reply `capSecond` returns a Bit built on
the unit payload of the first reply, and a literal leaf returns a Bit
built on the unit payload of the second reply.

## The opt-in quotient: the kept Bit as a constant

* `unit_eta`: the unit-η seed of the quotient, at its interface.
* `capSecond_ask_eqv`: `capSecond l₂` sent with the constant `y` is the
  labelled request `l₂` sent with `y` whose left reply takes the tree at
  `y`, whatever its payload. Unit η is used in two places: under the
  request, to move the kept Bit from the outer unit variable to literal
  unit, and after it, to discard the unit payload of the reply that the
  constant replaces. The rest is default Paper.
* `entryProgram_ask_eqv`: the same for `entryProgram l₁ l₂`, which keeps
  the state it was entered with across both of its requests. Sent with
  the constant `g` it is the two-request program sent with `g` whose
  return takes the tree at `g`.
* `capProgram_stepFactors`: the image of the factoring.
* `capRouter_eqv_capSource`: the table of `capProgram` rows equals its
  table of literal request trees at every original entry. A tree branch
  is indexed by the first reply, so the kept Bit is a constant in it.

## The opt-in quotient: completeness

* `capRouter_complete`, `capRouter_eqv_ltable_iff_valid`,
  `capRouter_eqv_duoRouter_iff_valid`: at given entries, a table of
  `capProgram` rows equals another one, any table of literal request
  trees, or a table of two-request programs exactly when the two are
  valid in every supported model. These use `LTable.eqv_iff_valid`, which
  depends on the phase-uniformity quotient and the request-prefix model.
  They are not statements about default Paper.

## Regression

`selSource sel` acts on `sel y y'` after the second left reply, where `y`
is the kept first payload and `y'` the second payload. For the one-row
table that returns the Bit it is given or repeats:

* `selSource_eqv_iff`: two such tables are equal exactly when the two
  choices are the same function.
* `capRouter_ne_duoRouter`: erasing the kept Bit is rejected. The table
  of `capProgram` rows differs from the table of two-request programs,
  which return the second payload.
* `capRouter_ne_flipped`: a wrong substitution is rejected. It differs
  from the trees that act on the negated kept payload.

## Scope

The table theorems are for `capProgram`: the kept Bit is the payload of
the first reply. For `entryProgram` only the request node sent with a
constant is proved here. Tables whose rows are `entryProgram` are treated
in `Composite.Entry`, by split states.

Whether `capSecond_ask_eqv` or `capRouter_eqv_capSource` fails in default
Paper is not decided here. No statement is made for the whole grammar of
written programs, and nothing is claimed about packed dispatchers in
general.
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

variable {K K₁ K₂ : Nat}

/-! ## The written programs -/

/-- The written region. Under the second request, `var 1` is the payload
of the first reply. The left leaf returns it. -/
theorem capProgram_written (l₁ l₂ : Bool) : (capProgram l₁ l₂).written =
    (.case (.op (.ask l₁) (.var 0))
      (.case (.op (.ask l₂) (.var 0)) (.br 0 (.var 1)) (.br 1 (.var 0)))
      (.br 1 (.var 0)) : Region signature.Instr) := rfl

/-- The second step. Under its request, `var 1` is its state. -/
theorem capSecond_written (l₂ : Bool) : (capSecond l₂).written =
    (.case (.op (.ask l₂) (.var 0)) (.br 0 (.var 1)) (.br 1 (.var 0)) : Region signature.Instr) := rfl

/-- Under the second request, `var 2` is the state the row was entered
with. The left leaf returns it. -/
theorem entryProgram_written (l₁ l₂ : Bool) : (entryProgram l₁ l₂).written =
    (.case (.op (.ask l₁) (.var 0))
      (.case (.op (.ask l₂) (.var 0)) (.br 0 (.var 2)) (.br 1 (.var 0)))
      (.br 1 (.var 0)) : Region signature.Instr) := rfl

/-! ## Default Paper: the factoring -/

/-- The written step of the program that keeps its first reply is the
step of its first request chained into the second step, as arrows of
default Paper. -/
theorem capProgram_step_arrow (l₁ l₂ : Bool) :
    ofRegion (step_typed (capProgram l₁ l₂)) =
      ofRegion (chainedStep_typed (labelPoll l₁).program (capSecond l₂)) :=
  Tables.cap_step_arrow l₁ l₂

/-- The table of such programs and the table whose trees send the second
step with the kept Bit as query have the same entered loops, as arrows of
default Paper. -/
theorem capRouter_arrow_carried (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    ofRegion ((capRouter l₁ l₂ act).entered_typed j) = ofRegion ((capCarried l₁ l₂ act).entered_typed j) :=
  Tables.cap_carried_arrow l₁ l₂ act j

/-! ## The opt-in quotient: the kept Bit as a constant -/

/-- Unit η holds in the opt-in quotient. It is an existing seed. -/
theorem unit_eta :
    Eqv false [(Ty.unit : Ty Empty)] (.br 0 .unit : Region signature.Instr) (.br 0 (.var 0)) [Ty.unit] :=
  Tables.unit_eta

/-- The second step sent with the constant `y` is the labelled request
sent with `y` whose left reply takes the tree at `y`. -/
theorem capSecond_ask_eqv (K : Nat) (l₂ y : Bool) (kids : Bool → Bool → Tree K) :
    Eqv false [(Ty.unit : Ty Empty)] (treeRegion K (.ask y (capSecond l₂) kids))
      (treeRegion K (.ask y (labelPoll l₂).program (keptKids kids y))) [Silmaril.coprod Bit (States K)] :=
  Tables.kept_ask_eqv K l₂ y kids

/-- The program that keeps its entry state, sent with the constant `g`,
is the two-request program sent with `g` whose return takes the tree at
`g`. -/
theorem entryProgram_ask_eqv (K : Nat) (l₁ l₂ g : Bool) (kids : Bool → Bool → Tree K) :
    Eqv false [(Ty.unit : Ty Empty)] (treeRegion K (.ask g (entryProgram l₁ l₂) kids))
      (treeRegion K (.ask g (duoProgram l₁ l₂) (keptKids kids g))) [Silmaril.coprod Bit (States K)] :=
  Tables.entry_ask_eqv K l₁ l₂ g kids

/-- The factoring in the opt-in quotient. It is the image of
`capProgram_step_arrow`. -/
theorem capProgram_stepFactors (l₁ l₂ : Bool) :
    StepFactors (capProgram l₁ l₂) (labelPoll l₁).program (capSecond l₂) :=
  Tables.cap_stepFactors l₁ l₂

/-- The table of programs that keep their first reply equals its table of
literal request trees at every entry. -/
theorem capRouter_eqv_capSource (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    Eqv false [State] ((capRouter l₁ l₂ act).entered j) ((capSource l₁ l₂ act).entered j) [Bit] :=
  Tables.cap_table_eqv l₁ l₂ act j

/-! ## The opt-in quotient: completeness -/

/-- Two tables of programs that keep their first reply are equal at given
entries exactly when they are valid in every supported model. -/
theorem capRouter_complete (l₁ l₂ : Fin (K₁ + 1) → Bool) (act : Fin (K₁ + 1) → Bool → Bool → Act K₁)
    (m₁ m₂ : Fin (K₂ + 1) → Bool) (act' : Fin (K₂ + 1) → Bool → Bool → Act K₂) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((capRouter l₁ l₂ act).entered i₁) ((capRouter m₁ m₂ act').entered i₂) [Bit] ↔
      Valid ((capRouter l₁ l₂ act).entered_typed i₁).hasType
        ((capRouter m₁ m₂ act').entered_typed i₂).hasType :=
  Tables.sources_complete ((capRouter l₁ l₂ act).entered_typed i₁) ((capRouter m₁ m₂ act').entered_typed i₂)
    (capSource l₁ l₂ act) (capSource m₁ m₂ act') i₁ i₂ (capRouter_eqv_capSource l₁ l₂ act i₁)
    (capRouter_eqv_capSource m₁ m₂ act' i₂)

/-- The same against any table of literal request trees. -/
theorem capRouter_eqv_ltable_iff_valid (l₁ l₂ : Fin (K₁ + 1) → Bool)
    (act : Fin (K₁ + 1) → Bool → Bool → Act K₁) (t : LTable K₂) (i₁ : Fin (K₁ + 1))
    (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((capRouter l₁ l₂ act).entered i₁) (t.entered i₂) [Bit] ↔
      Valid ((capRouter l₁ l₂ act).entered_typed i₁).hasType (t.entered_typed i₂).hasType :=
  Tables.sources_complete ((capRouter l₁ l₂ act).entered_typed i₁) (t.entered_typed i₂)
    (capSource l₁ l₂ act) t i₁ i₂ (capRouter_eqv_capSource l₁ l₂ act i₁)
    (Paper.Extension.Eqv.refl (t.entered_typed i₂).hasType)

/-- The same against a table of two-request programs, which do not keep
the first reply. -/
theorem capRouter_eqv_duoRouter_iff_valid (l₁ l₂ : Fin (K₁ + 1) → Bool)
    (act : Fin (K₁ + 1) → Bool → Bool → Act K₁) (m₁ m₂ : Fin (K₂ + 1) → Bool)
    (act' : Fin (K₂ + 1) → Bool → Bool → Act K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) :
    Eqv false [State] ((capRouter l₁ l₂ act).entered i₁) ((duoRouter m₁ m₂ act').entered i₂) [Bit] ↔
      Valid ((capRouter l₁ l₂ act).entered_typed i₁).hasType
        ((duoRouter m₁ m₂ act').entered_typed i₂).hasType :=
  Tables.sources_complete ((capRouter l₁ l₂ act).entered_typed i₁) ((duoRouter m₁ m₂ act').entered_typed i₂)
    (capSource l₁ l₂ act) (duoSource m₁ m₂ act') i₁ i₂ (capRouter_eqv_capSource l₁ l₂ act i₁)
    (duoRouter_eqv_duoSource m₁ m₂ act' i₂)

/-! ## Regression -/

/-- For the one-row table that returns the Bit it is given, two choices
of that Bit give equal loops exactly when they are the same choice. -/
theorem selSource_eqv_iff (l₁ l₂ : Bool) (sel sel' : Bool → Bool → Bool) :
    Eqv false [State] ((selSource sel (fun _ => l₁) (fun _ => l₂) echoAct).entered 0)
      ((selSource sel' (fun _ => l₁) (fun _ => l₂) echoAct).entered 0) [Bit] ↔ sel = sel' :=
  Tables.sel_eqv_iff l₁ l₂ sel sel'

/-- Erasing the kept Bit is observable: the program that keeps its first
reply differs from the two-request program, which returns the second. -/
theorem capRouter_ne_duoRouter (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((capRouter (fun _ => l₁) (fun _ => l₂) echoAct).entered 0)
      ((duoRouter (fun _ => l₁) (fun _ => l₂) echoAct).entered 0) [Bit] :=
  Tables.cap_ne_duo l₁ l₂

/-- Substituting the negated Bit for the kept one is observable. -/
theorem capRouter_ne_flipped (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((capRouter (fun _ => l₁) (fun _ => l₂) echoAct).entered 0)
      ((selSource flipFirst (fun _ => l₁) (fun _ => l₂) echoAct).entered 0) [Bit] :=
  Tables.cap_ne_flipped l₁ l₂

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
