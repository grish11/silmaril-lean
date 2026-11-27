module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.PollTable.Defs

/-! # Reading a scoped flat graph as a table of the polling fragment

`PollTable.read g` matches the constructors of a scoped flat graph
`g : FiniteCFG signature.Instr 2 1 1` against the exact shape of
`PollTable.flat`:

* the entry is a jump to block `0` or `1` with the input, variable `0`;
* each block is a case on one request whose operand is the block
  parameter, variable `0`;
* each arm of the case is a jump to a label with the reply payload,
  variable `0`.

It returns `none` for every other graph. `none` means that the graph is
not written in this shape. It says nothing about which sources the graph
is equal to.

The file also contains graphs used as tests: two accepted graphs written
directly in flat syntax, and graphs that miss the shape in one place.
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
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)

/-- Scoped terms of the flat syntax. -/
abbrev STm (n : Nat) : Type := _root_.Silmaril.Isotope.LetCase.LocallyNameless.Tm Empty signature.Instr n

/-! ## The reader -/

/-- Whether a scoped term is the newest variable. -/
def isBv0 {n : Nat} : STm (n + 1) → Bool
  | .bv i => decide (i = 0)
  | _ => false

/-- The label of a request. -/
def opLabel : signature.Instr → Bool
  | .ask l => l

/-- The leaf that jumps to a label of the graph. -/
def leafOfFin : Fin 3 → PollLeaf
  | 0 => .goto false
  | 1 => .goto true
  | 2 => .exit

/-- The block that a label of the graph names, if it is a block. -/
def startOfFin : Fin 3 → Option Bool
  | 0 => some false
  | 1 => some true
  | 2 => none

/-- An arm of a block: a jump with the reply payload. -/
def readLeaf : LambdaSSA.Flat signature.Instr 3 3 → Option PollLeaf
  | .br i a => if isBv0 a then some (leafOfFin i) else none
  | _ => none

/-- The scrutinee of a block: one request on the block parameter. -/
def readOp : STm 2 → Option Bool
  | .op f a => if isBv0 a then some (opLabel f) else none
  | _ => none

/-- A block: a case on one request, with two jumping arms. -/
def readBlock : LambdaSSA.Flat signature.Instr 3 2 → Option (Bool × PollLeaf × PollLeaf)
  | .case e l r =>
    (readOp e).bind fun lab => (readLeaf l).bind fun b₁ => (readLeaf r).map fun b₂ => (lab, b₁, b₂)
  | _ => none

/-- The entry: a jump to a block with the input. -/
def readEntry : LambdaSSA.Flat signature.Instr 3 1 → Option Bool
  | .br i a => if isBv0 a then startOfFin i else none
  | _ => none

/-- The table of two blocks read separately. -/
def PollTable.ofRows (s : Bool) (r₀ r₁ : Bool × PollLeaf × PollLeaf) : PollTable where
  label := fun c => match c with
    | false => r₀.1
    | true => r₁.1
  branch := fun c tag => match c, tag with
    | false, false => r₀.2.1
    | false, true => r₀.2.2
    | true, false => r₁.2.1
    | true, true => r₁.2.2
  start := s

/-- Read a scoped flat graph as a table of the fragment. -/
def PollTable.read (g : LambdaSSA.FiniteCFG signature.Instr 2 1 1) : Option PollTable :=
  (readEntry g.entry).bind fun s => (readBlock (g.block 0)).bind fun r₀ =>
    (readBlock (g.block 1)).map fun r₁ => PollTable.ofRows s r₀ r₁

/-! ## Accepted graphs, written in flat syntax -/

/-- Each block leaves on the left reply and repeats itself on the right. -/
def selfLit (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .case (.op (.ask l) (.bv 0)) (.br 2 (.bv 0)) (.br 0 (.bv 0))
    | 1 => .case (.op (.ask l) (.bv 0)) (.br 2 (.bv 0)) (.br 1 (.bv 0))

/-- Each block leaves on the left reply and goes to the other block on
the right. -/
def swapLit (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .case (.op (.ask l) (.bv 0)) (.br 2 (.bv 0)) (.br 1 (.bv 0))
    | 1 => .case (.op (.ask l) (.bv 0)) (.br 2 (.bv 0)) (.br 0 (.bv 0))

/-! ## Near misses -/

/-- A block of the fragment, used as the second block of the near misses. -/
def okBlock (l : Bool) : LambdaSSA.Flat signature.Instr 3 2 :=
  .case (.op (.ask l) (.bv 0)) (.br 2 (.bv 0)) (.br 1 (.bv 0))

/-- Wrong query: the request is sent with the captured input, variable `1`. -/
def queryMiss (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .case (.op (.ask l) (.bv 1)) (.br 2 (.bv 0)) (.br 0 (.bv 0))
    | 1 => okBlock l

/-- Wrong carrier: an arm jumps with the block parameter, variable `1`,
not with the reply payload. -/
def carrierMiss (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .case (.op (.ask l) (.bv 0)) (.br 2 (.bv 0)) (.br 0 (.bv 1))
    | 1 => okBlock l

/-- Captured read: an arm leaves with the captured input, variable `2`. -/
def captureMiss (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .case (.op (.ask l) (.bv 0)) (.br 2 (.bv 2)) (.br 0 (.bv 0))
    | 1 => okBlock l

/-- Silent jump: a block jumps without a request. -/
def silentMiss (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .br 1 (.bv 0)
    | 1 => okBlock l

/-- The entry leaves at once. -/
def entryMiss (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 2 (.bv 0)
  block := fun _ => okBlock l

/-- A block of the fragment behind a let that renames its parameter. The
reader rejects it; its source is nevertheless the source of `selfLit`. -/
def aliasMiss (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .let₁ (.bv 0) (.case (.op (.ask l) (.bv 0)) (.br 2 (.bv 0)) (.br 0 (.bv 0)))
    | 1 => okBlock l

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
