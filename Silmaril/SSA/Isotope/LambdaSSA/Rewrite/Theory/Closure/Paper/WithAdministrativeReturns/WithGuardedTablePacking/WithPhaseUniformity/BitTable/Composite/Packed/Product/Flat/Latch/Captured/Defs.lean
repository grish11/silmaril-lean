module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Defs

/-! # A two-block cyclic flat source whose header uses the captured input

The scoped flat graph `captFlat l` has two blocks, one exit and one
captured input `c`, a Bit. Its entry jumps to the header with `c`.

* The header receives a Bit `y` and sends the request `l` with `y`. On
  the left reply it jumps to the exit with the captured input `c`. On the
  right reply `r` it jumps to the back-edge block with `r`.
* The back-edge block has its own parameter and jumps to the header.

The header reads the captured input, so this graph is written in the
scoped flat layer: the elaborator of named tables gives a block only its
parameter.

`captSource l` is its region and `captReadback l` its packed readback,
whose loop state `CaptState` is the captured input paired with the tagged
parameters.

`keepCase` is the tail of a row that keeps the captured input in the
state and returns it. `pollBody l` is the capture-free step of the header
on its parameter, `captBody l` the step on the pair of the captured input
and the parameter, and `captLoop l` the loop of `captBody l` entered with
the input in both places.

`captRouter l` is the two-row router table that `captBody l` should
correspond to, and `Task.captStep l` the equation between the conjugated
step and the dispatcher step of that table. It is not proved.
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

/-! ## The tail that keeps and returns the captured input -/

/-- Distribute the captured input over the sum exit of a step. On the
return side discard the returned value and return the captured input. -/
def keepCase : Region signature.Instr :=
  .let₂ (.var 0) (.case (.var 0) (.br 0 (.inl (.var 2))) (.br 0 (.inr (.pair (.var 2) (.var 0)))))

theorem keepCase_typed {X E A : Ty Empty} :
    ValueBranches [Silmaril.product X (Silmaril.coprod E A)] keepCase
      [Silmaril.coprod X (Silmaril.product X A)] :=
  .let₂ (A := X) (B := Silmaril.coprod E A) (.var rfl)
    (.case (A := E) (B := A) (.var rfl) (.br rfl (.inl (.var rfl)))
      (.br rfl (.inr (.pair (.var rfl) (.var rfl)))))

/-- The first component of a pair. -/
def fstRegion : Region signature.Instr := .let₂ (.var 0) (.br 0 (.var 1))

theorem fstRegion_typed {X E : Ty Empty} :
    ValueBranches [Silmaril.product X E] (fstRegion : Region signature.Instr) [X] :=
  .let₂ (A := X) (B := E) (.var rfl) (.br rfl (.var rfl))

/-! ## The source -/

/-- The scoped flat graph: the header at label `0` reads the captured
input at its exit, the back-edge block is at label `1`, the exit at
label `2`. -/
def captFlat (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .case (.op (.ask l) (.bv 0)) (.br 2 (.bv 2)) (.br 1 (.bv 0))
    | 1 => .br 0 (.bv 0)

/-- The header block: variable `0` is its parameter and variable `1` the
captured input, which it sends to the exit. -/
def captHead (l : Bool) : Region signature.Instr :=
  .case (.op (.ask l) (.var 0)) (.br 2 (.var 2)) (.br 1 (.var 0))

/-- The blocks of the table. The header uses the captured input. -/
def captBlocks (l : Bool) (i : Fin 2) : Region signature.Instr :=
  match i with
  | 0 => captHead l
  | 1 => latchBlock.renameVars (lift Nat.succ)

/-- The region of the flat source. -/
def captSource (l : Bool) : Region signature.Instr := (captFlat l).erase

theorem captSource_eq (l : Bool) : captSource l = .cfg (.br 0 (.var 0)) 2 (captBlocks l) := by
  refine congrArg (Region.cfg _ 2) (funext fun i => ?_)
  match i with
  | 0 => rfl
  | 1 => rfl

theorem captEntry_typed :
    ValueBranches [Bit] (.br 0 (.var 0) : Region signature.Instr)
      (List.ofFn (fun _ : Fin 2 => Bit) ++ [Bit]) :=
  .br (ℓ := 0) (A := Bit) rfl (.var rfl)

theorem captHead_typed (l : Bool) : ValueBranches [Bit, Bit] (captHead l) [Bit, Bit, Bit] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br (ℓ := 2) (A := Bit) rfl (.var (i := 2) rfl))
    (.br (ℓ := 1) (A := Bit) rfl (.var (i := 0) rfl))

theorem captBlocks_typed (l : Bool) (i : Fin 2) :
    ValueBranches [Bit, Bit] (captBlocks l i) (List.ofFn (fun _ : Fin 2 => Bit) ++ [Bit]) :=
  match i with
  | 0 => captHead_typed l
  | 1 => (ValueBranches.br (ℓ := 0) (A := Bit) (L := [Bit, Bit, Bit]) rfl (.var (i := 0) rfl)).renameVars
      (headerRen (S := Bit))

/-- The source is a guarded table at the entry `Bit` with exit `Bit`. -/
theorem captSource_typed (l : Bool) : ValueBranches [Bit] (captSource l) [Bit] :=
  captSource_eq l ▸ .cfg (fun _ : Fin 2 => Bit) captEntry_typed (captBlocks_typed l)

/-- The packed readback of the table. -/
noncomputable def captReadback (l : Bool) : {r : Region signature.Instr // ValueBranches [Bit] r [Bit]} :=
  packedReadbackRep (fun _ : Fin 2 => Bit) captEntry_typed (captBlocks_typed l)

/-- The tagged parameters of the two blocks. -/
abbrev CaptTags : Ty Empty := packedExitType [Bit, Bit]

/-- The state of the readback loop: the captured input paired with the
tagged parameters. -/
abbrev CaptState : Ty Empty := Silmaril.product Bit CaptTags

/-! ## Rows and steps -/

/-- The row of the header in the packed readback. On the left reply it
returns the captured input. -/
def captHeadRow (l : Bool) : Region signature.Instr :=
  .let₂ (.var 0) (.case (.op (.ask l) (.var 0)) (.br 0 (.inl (.var 2)))
    (.br 0 (.inr (.pair (.var 2) (.inr (.inl (.var 0)))))))

theorem captHeadRow_typed (l : Bool) :
    ValueBranches [Silmaril.product Bit Bit] (captHeadRow l) [Silmaril.coprod Bit CaptState] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var (i := 2) rfl)))
      (.br rfl (.inr (.pair (.var (i := 2) rfl) (.inr (.inl (.var (i := 0) rfl)))))))

theorem captLatchRow_typed :
    ValueBranches [Silmaril.product Bit Bit] (latchRow : Region signature.Instr)
      [Silmaril.coprod Bit CaptState] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl) (.br rfl (.inr (.pair (.var rfl) (.inl (.var rfl)))))

/-- The header as a capture-free step on its parameter: return the reply
payload, or continue at the tag of the back-edge block. -/
def pollHead (l : Bool) : Region signature.Instr :=
  .case (.op (.ask l) (.var 0)) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.inr (.inl (.var 0)))))

theorem pollHead_typed (l : Bool) : ValueBranches [Bit] (pollHead l) [Silmaril.coprod Bit CaptTags] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var rfl)))
    (.br rfl (.inr (.inr (.inl (.var rfl)))))

/-- The capture-free step of the header on its parameter: send the
request, return the left reply or repeat with the right reply. -/
def pollBody (l : Bool) : Region signature.Instr :=
  .case (.op (.ask l) (.var 0)) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.var 0)))

theorem pollBody_typed (l : Bool) : ValueBranches [Bit] (pollBody l) [Silmaril.coprod Bit Bit] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var rfl))) (.br rfl (.inr (.var rfl)))

/-- The step on the pair `(c, y)` of the captured input and the header
parameter: send the request with `y`; on the left reply return `c`; on
the right reply `r` repeat with `(c, r)`. The first component is fixed. -/
def captBody (l : Bool) : Region signature.Instr :=
  .let₂ (.var 0) (.case (.op (.ask l) (.var 0)) (.br 0 (.inl (.var 2)))
    (.br 0 (.inr (.pair (.var 2) (.var 0)))))

theorem captBody_typed (l : Bool) : ValueBranches [Pair] (captBody l) [Silmaril.coprod Bit Pair] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var (i := 2) rfl)))
      (.br rfl (.inr (.pair (.var (i := 2) rfl) (.var (i := 0) rfl)))))

/-- Enter with the input as the captured component and as the first
parameter of the header. -/
def dupEntry : Region signature.Instr := .br 0 (.pair (.var 0) (.var 0))

theorem dupEntry_typed : ValueBranches [Bit] (dupEntry : Region signature.Instr) [Pair] :=
  .br rfl (.pair (.var rfl) (.var rfl))

/-- The loop on the pair of captured input and parameter, entered with
the input in both places. -/
def captLoop (l : Bool) : Region signature.Instr := seqRegion dupEntry (loopRegion Pair (captBody l))

theorem captLoop_typed (l : Bool) : ValueBranches [Bit] (captLoop l) [Bit] :=
  seqRegion_typed dupEntry_typed (loopRegion_typed (captBody_typed l))

/-! ## The router table of the step, and the open step equation -/

/-- The router table of `captBody`: the row is the captured input and the
carried Bit is the header parameter. The left reply returns the row's
Bit. The right reply stays in the row, carrying the reply. -/
def captAct (i : Fin 2) (x pl : Bool) : Act 1 :=
  match x with
  | false => .ret (pairBit i)
  | true => .go i pl

def captRouter (l : Bool) : Router 1 := Router.ofLabels (fun _ => l) captAct

/-- The step equation for `captBody`: conjugated by the encoding of
pairs, the step is the dispatcher step of `captRouter l`. Not proved. -/
def Task.captStep (l : Bool) : Prop :=
  Eqv false [States 1] (seqRegion pairDec (seqRegion (captBody l) (postRegion pairEnc)))
    (dispatch 1 (captRouter l).rows) [Silmaril.coprod Bit (States 1)]

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
