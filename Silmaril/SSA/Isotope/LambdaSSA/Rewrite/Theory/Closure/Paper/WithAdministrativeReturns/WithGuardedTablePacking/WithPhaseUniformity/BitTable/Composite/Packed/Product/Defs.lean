module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Defs

/-! # A pair of Bits and the packed state of two rows

`Pair` is the product of two Bits. `States 1` is the packed state of two
rows: a tagged sum of two Bits.

* `pairEnc : Pair → States 1` destructures the pair and cases on the
  first Bit: the first Bit selects the row and the second is carried.
* `pairDec : States 1 → Pair` pairs the constant of the row with the
  carried Bit.

`postRegion d` applies `d` to the repeated state of a step.
`loopRegion S body` is the loop on `S` with step `body`.

`pairBody l` is a step written on pairs, `pairRouter l` the router table
it corresponds to, and `Task.pairStep l` the equation between the
conjugated body and the dispatcher step of that table. That equation is
open: it is stated here and not proved.
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


variable {K : Nat}

/-- A pair of Bits. -/
abbrev Pair : Ty Empty := Silmaril.product Bit Bit

/-- Encode a pair: a case on its first Bit selects the row, and its
second Bit is carried. -/
def pairEnc : Region signature.Instr :=
  .let₂ (.var 0) (.case (.var 1) (.br 0 (.inl (.inl (.var 1)))) (.br 0 (.inr (.inl (.var 1)))))

theorem pairEnc_typed : ValueBranches [Pair] pairEnc [States 1] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Ty.unit) (B := Ty.unit) (.var rfl) (.br rfl (.inl (.inl (.var rfl))))
      (.br rfl (.inr (.inl (.var rfl)))))

/-- The pair whose first Bit is the constant `c`. -/
def pairLit (c : Bool) : Region signature.Instr := .br 0 (.pair (litBit c) (.var 0))

theorem pairLit_typed (c : Bool) : ValueBranches [Bit] (pairLit c) [Pair] :=
  .br rfl (.pair (litBit_typed c) (.var rfl))

theorem pairDead_typed :
    ValueBranches [Silmaril.empty] (.br 0 (.pair (.inl .unit) (.inl .unit)) : Region signature.Instr) [Pair] :=
  .br rfl (.pair (.inl .unit) (.inl .unit))

/-- Decode the row of the constant `c`: pair `c` with the carried Bit. -/
def pairDecRow (c : Bool) : Region signature.Instr :=
  .case (.var 0) ((pairLit c).renameVars (lift Nat.succ))
    ((Region.br 0 (.pair (.inl .unit) (.inl .unit))).renameVars (lift Nat.succ))

theorem pairDecRow_typed (c : Bool) : ValueBranches [State] (pairDecRow c) [Pair] :=
  caseValueBranches (pairLit_typed c) pairDead_typed

def pairBit (i : Fin 2) : Bool :=
  match i with
  | 0 => false
  | 1 => true

def pairIdx (c : Bool) : Fin 2 :=
  match c with
  | false => 0
  | true => 1

/-- Decode a packed state of two rows to a pair. -/
def pairDec : Region signature.Instr := dispatch 1 fun i => pairDecRow (pairBit i)

theorem pairDec_typed : ValueBranches [States 1] pairDec [Pair] :=
  dispatch_typed 1 fun i => pairDecRow_typed (pairBit i)

/-- Apply `d` to the repeated state of a step and keep its result. -/
def postRegion (d : Region signature.Instr) : Region signature.Instr :=
  .case (.var 0) ((Region.br 0 (.inl (.var 0))).renameVars (lift Nat.succ))
    ((seqRegion d (.br 0 (.inr (.var 0)))).renameVars (lift Nat.succ))

theorem postRegion_typed {X Y B : Ty Empty} {d : Region signature.Instr} (hd : ValueBranches [X] d [Y]) :
    ValueBranches [Silmaril.coprod B X] (postRegion d) [Silmaril.coprod B Y] :=
  caseValueBranches (.br rfl (.inl (.var rfl))) (seqRegion_typed hd (.br rfl (.inr (.var rfl))))

/-- A loop whose step is `body`, on the state type `S`. -/
def loopRegion (S : Ty Empty) (body : Region signature.Instr) : Region signature.Instr :=
  SyntacticCategory.iterateRegion S body

theorem loopRegion_typed {S : Ty Empty} {body : Region signature.Instr}
    (h : ValueBranches [S] body [Silmaril.coprod Bit S]) : ValueBranches [S] (loopRegion S body) [Bit] :=
  SyntacticCategory.iterateRegion_valueBranches h

/-! ## A loop written on pairs -/

/-- A step written on a pair `(x, y)`. It sends the request `l` with the
second Bit `y` as query. On the left reply it returns the first Bit `x`.
On the right reply `r` it repeats with the pair `(r, x)`. -/
def pairBody (l : Bool) : Region signature.Instr :=
  .let₂ (.var 0)
    (.case (.op (.ask l) (.var 0)) (.br 0 (.inl (.var 2))) (.br 0 (.inr (.pair (.var 0) (.var 2)))))

theorem pairBody_typed (l : Bool) : ValueBranches [Pair] (pairBody l) [Silmaril.coprod Bit Pair] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var rfl)))
      (.br rfl (.inr (.pair (.var rfl) (.var rfl)))))

/-- The router table of that step: the row is the first Bit and the
carried Bit is the second. The left reply returns the row's Bit. The
right reply goes to the row of its payload, carrying the row's Bit. -/
def pairAct (i : Fin 2) (x pl : Bool) : Act 1 :=
  match x with
  | false => .ret (pairBit i)
  | true => .go (pairIdx pl) (pairBit i)

def pairRouter (l : Bool) : Router 1 := Router.ofLabels (fun _ => l) pairAct

namespace Task

/-- Open: the body on pairs, conjugated by the encoding, is the dispatcher
step of `pairRouter l`. -/
def pairStep (l : Bool) : Prop :=
  Eqv false [States 1] (seqRegion pairDec (seqRegion (pairBody l) (postRegion pairEnc)))
    (dispatch 1 (pairRouter l).rows) [Silmaril.coprod Bit (States 1)]

end Task

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
