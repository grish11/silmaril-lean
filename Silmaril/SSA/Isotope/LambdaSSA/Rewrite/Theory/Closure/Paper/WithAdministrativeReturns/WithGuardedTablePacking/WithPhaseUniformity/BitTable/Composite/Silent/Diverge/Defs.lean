module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Router.Prefix.Defs

/-! # Router tables with the canonical silent row

`Router.ofSpin label act` is a router table whose rows are labelled
requests (`label i = some l`) or canonical silent rows (`label i = none`).
A silent row is the row of `spinRouter`: it sends nothing and repeats to
itself with `false`. A reply after which the table diverges silently
repeats to a silent row: that is the divergent leaf. A table of labelled
rows is the case with no silent row.

`Tidy` says that a repeat to a silent row carries `false`. `Sighted` says
that every labelled row has a reply after which something is observed: a
return, or a repeat to a labelled row. A row without one is blind.

## Mixed tables of single requests

`Polled row` says that every request row of a mixed table is one labelled
request. `spunRouter row act cyc fuel` is the mixed table as a table with
silent rows, on its split states: a request row keeps its label and takes
its resolved actions, with the Bits carried into `cyc` replaced by
`false`; every request-free split state is a silent row. `Classed` is
the classification of `Classified` without the condition on request
rows. `SpinPointed r label act x` says that `r` entered with each
constant `q` is `Router.ofSpin label act` entered with `q` at `x q`.

## Regression tables

`veerRow` is a request row in front of a request-free row. With
`veerAct n f` the left reply of the request leads into the request-free
row, which is a silent cycle; `n` negates the Bit on the way in and `f`
makes the cycle negate it. With `veerRet` the left reply returns, and
with `veerAgain` it sends the request again.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)


variable {M : Nat}

/-- The program of a row: one labelled request, or the canonical silent
row. -/
def lsProg (o : Option Bool) : Program :=
  match o with
  | some l => (labelPoll l).program
  | none => .ret 0 0

/-- The actions of a row. The silent row repeats to itself with `false`. -/
def lsAct (o : Option Bool) (i : Fin (M + 1)) (a : Bool → Bool → Act M) : Bool → Bool → Act M :=
  match o with
  | some _ => a
  | none => fun _ _ => .go i false

/-- A router table whose rows are labelled requests or canonical silent
rows. A reply that leads to silent divergence repeats to a silent row. -/
def Router.ofSpin (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M) : Router M :=
  ⟨fun i => lsProg (label i), fun i => lsAct (label i) i (act i)⟩

/-- A repeat to a silent row carries `false`. -/
def Tidy (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M) : Prop :=
  ∀ i l, label i = some l → ∀ tag pl j q, act i tag pl = .go j q → label j = none → q = false

/-- The action returns or repeats to a labelled row: something is
observed after it. -/
def Act.Seen (label : Fin (M + 1) → Option Bool) : Act M → Prop
  | .ret _ => True
  | .go j _ => ∃ l, label j = some l

/-- Every labelled row has a reply after which something is observed.
A row without one is blind: its query is never observed. -/
def Sighted (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M) : Prop :=
  ∀ i l, label i = some l → ∃ tag pl, (act i tag pl).Seen label

/-! ## Mixed tables whose request rows are single requests -/

variable {K : Nat}

/-- The label of a split state: the label of a request row, and `none`
at a request-free row. -/
def MixRow.pollLabel : MixRow → Option Bool
  | .ask r => some r.label
  | .pure _ => none

/-- Every request row is one labelled request. -/
def Polled (row : Fin (K + 1) → MixRow) : Prop :=
  ∀ i r, row i = .ask r → r = ⟨r.label, .ret 0 0, .ret 1 0⟩

def spunLabel (row : Fin (K + 1) → MixRow) (x : Fin (K + (K + 1) + 1)) : Option Bool :=
  (row (splitRow x)).pollLabel

/-- The resolved actions of the split states, with the Bits carried into
the closed silent set replaced by `false`. -/
def spunAct (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (cyc : Fin (K + (K + 1) + 1) → Bool) (fuel : Nat) (x : Fin (K + (K + 1) + 1)) (a b : Bool) :
    Act (K + (K + 1)) :=
  dullAct cyc (resolveN (cutSil (mixSil row act) cyc) fuel (redirect (act (splitRow x) a b)))

/-- The mixed table as a router table of labelled rows and canonical
silent rows: each request-free split state is a silent row. -/
def spunRouter (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (cyc : Fin (K + (K + 1) + 1) → Bool) (fuel : Nat) : Router (K + (K + 1)) :=
  Router.ofSpin (spunLabel row) (spunAct row act cyc fuel)

/-- A classification without the condition on request rows: `cyc` is
closed and the fuel resolves every action. -/
structure Classed (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (cyc : Fin (K + (K + 1) + 1) → Bool) (fuel : Nat) : Prop where
  cyclic : Cyclic (mixSil row act) cyc
  settled : ∀ a, (resolveN (cutSil (mixSil row act) cyc) fuel a).Settled (cutSil (mixSil row act) cyc)

/-- `r` entered with each constant is a router table with silent rows
entered with that constant. -/
def SpinPointed (r : Region signature.Instr) (label : Fin (M + 1) → Option Bool)
    (act : Fin (M + 1) → Bool → Bool → Act M) (x : Bool → Fin (M + 1)) : Prop :=
  ∀ q, Eqv false [Ty.unit] (constEntry q r) (constEntry q ((Router.ofSpin label act).entered (x q))) [Bit]

/-! ## Regression tables -/

/-- A request row in front of a request-free row. -/
def veerRow (l : Bool) (i : Fin 2) : MixRow :=
  match i with
  | 0 => .ask ⟨l, .ret 0 0, .ret 1 0⟩
  | 1 => .pure 1

/-- The left reply of the request leads into row one, with the reply
negated when `n`. The right reply returns. Row one is a silent cycle that
negates the Bit when `f`. -/
def veerAct (n f : Bool) (i : Fin 2) (x g : Bool) : Act 1 :=
  match i, x with
  | 0, false => .go 1 (n != g)
  | 0, true => .ret g
  | 1, _ => .go 1 (f != g)

/-- The left reply returns instead. -/
def veerRet (i : Fin 2) (x g : Bool) : Act 1 :=
  match i, x with
  | 0, _ => .ret g
  | 1, _ => .go 1 (!g)

/-- The left reply sends the request again instead. -/
def veerAgain (i : Fin 2) (x g : Bool) : Act 1 :=
  match i, x with
  | 0, false => .go 0 g
  | 0, true => .ret g
  | 1, _ => .go 1 (!g)

/-- The split states of row one. -/
def veerCyc (x : Fin (1 + (1 + 1) + 1)) : Bool :=
  match x with
  | 1 => true
  | 3 => true
  | _ => false

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
