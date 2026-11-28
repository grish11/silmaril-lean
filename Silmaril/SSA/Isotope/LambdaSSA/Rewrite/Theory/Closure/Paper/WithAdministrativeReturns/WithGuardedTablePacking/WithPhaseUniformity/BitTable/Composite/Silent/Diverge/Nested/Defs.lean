module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Query.Defs

/-! # Nested request rows with silent divergence

## Request trees with silent rows

`Tree.Tidy spin` says that every repeat of a request tree into a silent
state carries `false`. `TreeTable.Spun` says that each row of a table of
request trees is a labelled request whose trees are tidy trees of
labelled requests, or the canonical silent row, which repeats to itself
with `false`.

## The split table of a mixed table

On the split states of a mixed table, `nestRouter` has the written
program of each request row, with its resolved actions and with the Bits
carried into `cyc` replaced by `false`, and a canonical silent row at
every request-free state. `nestBit` is the Bit a split state is entered
with: its own Bit at a request row, `false` at a silent row. `nestTrees`
is the same table with each request row specialized at that Bit to its
literal request trees.

## Landings

A `TLanding` is a returned Bit or a table of request trees entered with a
constant; `nestLanding row act cyc fuel j q` is where row `j` lands when
entered with `q`. An `SLanding` is a returned Bit or a router table of
labelled rows and canonical silent rows entered with a constant. A
landing at a silent row is silent divergence. `SLanded r L` says that `r`
entered with each constant `q` is `L q`, in the opt-in quotient.

## Regression tables

`stashRow l₁ l₂ s` is a request row in front of a request-free row. On
its left reply the request row sends a second request, queried with the
stored first reply, or with the entry Bit when `s`. With `stashAct n f`
both replies of the second request lead into the request-free row, which
is a silent cycle, so the second request is blind. `stashLabel` and
`stashSpun s n` are the explicit table: four blind rows, two copies of
the request row and two silent rows.
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


variable {K M : Nat}

/-! ## Request trees with silent rows -/

/-- Every repeat of the tree into a silent state carries `false`. -/
def Tree.Tidy (spin : Fin (M + 1) → Prop) : Tree M → Prop
  | .leaf (.ret _) => True
  | .leaf (.go z q) => spin z → q = false
  | .ask _ _ kids => ∀ x y, (kids x y).Tidy spin

/-- A table of request trees whose rows are labelled requests, with tidy
trees of labelled requests, or canonical silent rows. -/
def TreeTable.Spun (t : TreeTable M) : Prop :=
  ∀ j, (IsLabel (t.prog j) ∧
      ∀ x y, (t.kids j x y).All IsLabel ∧ (t.kids j x y).Tidy fun z => t.prog z = .ret 0 0) ∨
    (t.prog j = .ret 0 0 ∧ ∀ x y, t.kids j x y = .leaf (.go j false))

/-! ## The split table of a mixed table, as request trees -/

/-- The program of a split state: the written row, or the silent row. -/
def MixRow.liveProg : MixRow → Program
  | .ask r => r.program
  | .pure _ => .ret 0 0

def MixRow.liveAct (m : MixRow) (y : Fin (M + 1)) (a : Bool → Bool → Act M) : Bool → Bool → Act M :=
  match m with
  | .ask _ => a
  | .pure _ => fun _ _ => .go y false

/-- The Bit a split state is entered with: `false` at a silent row. -/
def MixRow.liveBit (m : MixRow) (c : Bool) : Bool :=
  match m with
  | .ask _ => c
  | .pure _ => false

def MixRow.treeProg : MixRow → Program
  | .ask r => (labelPoll r.label).program
  | .pure _ => .ret 0 0

/-- The trees of a split state: the literal request trees of its row
entered with its Bit, or the silent row. -/
def MixRow.treeKids (m : MixRow) (y : Fin (M + 1)) (a : Bool → Bool → Act M) (c : Bool) :
    Bool → Bool → Tree M :=
  match m with
  | .ask r => fun x b => (r.kids a c x b).toTree
  | .pure _ => fun _ _ => .leaf (.go y false)

/-- The split table with written request rows and silent rows. The
actions are resolved, and the Bits carried into `cyc` are `false`. -/
def nestRouter (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (cyc : Fin (K + (K + 1) + 1) → Bool) (fuel : Nat) : Router (K + (K + 1)) :=
  ⟨fun y => (row (splitRow y)).liveProg,
    fun y => (row (splitRow y)).liveAct y (spunAct row act cyc fuel y)⟩

def nestBit (row : Fin (K + 1) → MixRow) (y : Fin (K + (K + 1) + 1)) : Bool :=
  (row (splitRow y)).liveBit (splitBit y)

/-- The split table as request trees with silent rows: each request row
is specialized at the Bit of its split state. -/
def nestTrees (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (cyc : Fin (K + (K + 1) + 1) → Bool) (fuel : Nat) : TreeTable (K + (K + 1)) :=
  ⟨fun y => (row (splitRow y)).treeProg,
    fun y => (row (splitRow y)).treeKids y (spunAct row act cyc fuel y) (nestBit row y)⟩

/-! ## Landings -/

/-- Where an entry lands: a returned Bit, or a table of request trees
entered with a constant. -/
inductive TLanding (M : Nat) where
  | ret (c : Bool)
  | at (t : TreeTable M) (x : Fin (M + 1)) (q : Bool)

def TLanding.region : TLanding M → Region signature.Instr
  | .ret c => .br 0 (bitTm c)
  | .at t x q => constEntry q (t.entered x)

theorem TLanding.region_typed (L : TLanding M) : ValueBranches [Ty.unit] L.region [Bit] := by
  cases L with
  | ret c => exact .br rfl (bitTm_typed c)
  | «at» t x q => exact constEntry_typed q (t.entered_typed x)

def TLanded (r : Region signature.Instr) (L : Bool → TLanding M) : Prop :=
  ∀ q, Eqv false [Ty.unit] (constEntry q r) (L q).region [Bit]

def Act.treeLanding (t : TreeTable M) (c : Fin (M + 1) → Bool) : Act M → TLanding M
  | .ret b => .ret b
  | .go y _ => .at t y (c y)

/-- Where row `j` of a mixed table lands when entered with `q`. -/
def nestLanding (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (cyc : Fin (K + (K + 1) + 1) → Bool) (fuel : Nat) (j : Fin (K + 1)) (q : Bool) : TLanding (K + (K + 1)) :=
  (resolveN (cutSil (mixSil row act) cyc) fuel (.go (splitIdx j q) q)).treeLanding
    (nestTrees row act cyc fuel) (nestBit row)

/-- Where an entry lands, with router tables: a returned Bit, or a table
of labelled rows and canonical silent rows entered with a constant. A
silent row there is silent divergence. -/
inductive SLanding where
  | ret (c : Bool)
  | at {M : Nat} (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M)
      (x : Fin (M + 1)) (q : Bool)

def SLanding.region : SLanding → Region signature.Instr
  | .ret c => .br 0 (bitTm c)
  | .at label act x q => constEntry q ((Router.ofSpin label act).entered x)

theorem SLanding.region_typed (L : SLanding) : ValueBranches [Ty.unit] L.region [Bit] := by
  cases L with
  | ret c => exact .br rfl (bitTm_typed c)
  | «at» label act x q => exact constEntry_typed q ((Router.ofSpin label act).entered_typed x)

def SLanding.Tidy : SLanding → Prop
  | .ret _ => True
  | .at label act _ _ => BitTable.Tidy label act

/-- `r` entered with each constant is its landing. -/
def SLanded (r : Region signature.Instr) (L : Bool → SLanding) : Prop :=
  ∀ q, Eqv false [Ty.unit] (constEntry q r) (L q).region [Bit]

/-! ## Regression tables -/

/-- A request row in front of a request-free row. On its left reply the
request row sends a second request, whose query is the first reply, or
the entry Bit when `s`. Both replies of the second request repeat. The
right reply of the first request returns. -/
def stashRow (l₁ l₂ s : Bool) (i : Fin 2) : MixRow :=
  match i with
  | 0 => .ask ⟨l₁, .ask l₂ (match s with | false => 0 | true => 1) (.ret 1 0) (.ret 1 0), .ret 0 0⟩
  | 1 => .pure 1

/-- A return is returned. A repeat leads into row one, with the Bit
negated when `n`. Row one is a silent cycle that negates the Bit when
`f`. So the second request is blind. -/
def stashAct (n f : Bool) (i : Fin 2) (x g : Bool) : Act 1 :=
  match i, x with
  | 0, false => .ret g
  | 0, true => .go 1 (n != g)
  | 1, _ => .go 1 (f != g)

def stashLabel (l₁ l₂ : Bool) (i : Fin 8) : Option Bool :=
  match i with
  | 0 => some l₂
  | 1 => some l₂
  | 2 => some l₂
  | 3 => some l₂
  | 4 => some l₁
  | 5 => none
  | 6 => some l₁
  | 7 => none

/-- The second request sent from the entry Bit `c` after the first reply `y`. -/
def stashInner (c y : Bool) : Fin 8 :=
  match c, y with
  | false, false => 0
  | false, true => 1
  | true, false => 2
  | true, true => 3

def stashSpin (b : Bool) : Fin 8 :=
  match b with
  | false => 5
  | true => 7

/-- The table with the second requests as four explicit blind rows, in
front of the two copies of the request row and the two silent rows. -/
def stashSpun (s n : Bool) (i : Fin 8) (x y : Bool) : Act 7 :=
  match i, x with
  | 0, _ => .go (stashSpin (n != y)) false
  | 1, _ => .go (stashSpin (n != y)) false
  | 2, _ => .go (stashSpin (n != y)) false
  | 3, _ => .go (stashSpin (n != y)) false
  | 4, false => .go (stashInner false y) (match s with | false => y | true => false)
  | 4, true => .ret y
  | 5, _ => .go 5 false
  | 6, false => .go (stashInner true y) (match s with | false => y | true => true)
  | 6, true => .ret y
  | 7, _ => .go 7 false

/-- The copy of the request row for the entry Bit `q`. -/
def stashEntry (q : Bool) : Fin 8 :=
  match q with
  | false => 4
  | true => 6

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
