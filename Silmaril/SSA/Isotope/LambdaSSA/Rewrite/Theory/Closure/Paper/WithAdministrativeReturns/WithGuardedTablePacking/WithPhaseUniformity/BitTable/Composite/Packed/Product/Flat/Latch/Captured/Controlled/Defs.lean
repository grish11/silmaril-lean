module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Latch.Captured.Defs

/-! # A two-block flat source whose captured input chooses the request

The scoped flat graph `ctrlFlat l₀ l₁` has two blocks, one exit and one
captured input `c`, a Bit. Its entry jumps to the header with `c`.

* The header receives a Bit `y` and cases on the captured input: it
  sends the request `l₀` when `c` is false and `l₁` when `c` is true,
  in both cases with `y` as the query. On the left reply it jumps to the
  exit with `c`. On the right reply `r` it jumps to the back-edge block
  with `r`.
* The back-edge block jumps to the header with its parameter.

`pickLabel l₀ l₁ c` is the label sent for the captured input `c`.
`ctrlSource l₀ l₁` is the region of the graph. `ctrlRouter l₀ l₁` is the
two-row router table whose row `c` has the label `pickLabel l₀ l₁ c`.
`ctrlBody l₀ l₁` is the step on the pair of captured input and header
parameter, and `ctrlLoop l₀ l₁` its loop entered with the input in both
places.
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

/-- The label sent for the captured input `c`. -/
def pickLabel (l₀ l₁ c : Bool) : Bool :=
  match c with
  | false => l₀
  | true => l₁

/-- The scoped flat graph: the header at label `0` cases on the captured
input to choose its request, the back-edge block is at label `1`, the
exit at label `2`. -/
def ctrlFlat (l₀ l₁ : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .case (.bv 1)
        (.case (.op (.ask l₀) (.bv 1)) (.br 2 (.bv 3)) (.br 1 (.bv 0)))
        (.case (.op (.ask l₁) (.bv 1)) (.br 2 (.bv 3)) (.br 1 (.bv 0)))
    | 1 => .br 0 (.bv 0)

/-- One arm of the header, under the unit payload of the case on the
captured input: variable `1` is the parameter and variable `2` the
captured input. -/
def ctrlArm (l : Bool) : Region signature.Instr :=
  .case (.op (.ask l) (.var 1)) (.br 2 (.var 3)) (.br 1 (.var 0))

/-- The header block: a case on the captured input, variable `1`. -/
def ctrlHead (l₀ l₁ : Bool) : Region signature.Instr :=
  .case (.var 1) (ctrlArm l₀) (ctrlArm l₁)

def ctrlBlocks (l₀ l₁ : Bool) (i : Fin 2) : Region signature.Instr :=
  match i with
  | 0 => ctrlHead l₀ l₁
  | 1 => latchBlock.renameVars (lift Nat.succ)

/-- The region of the flat source. -/
def ctrlSource (l₀ l₁ : Bool) : Region signature.Instr := (ctrlFlat l₀ l₁).erase

theorem ctrlSource_eq (l₀ l₁ : Bool) : ctrlSource l₀ l₁ = .cfg (.br 0 (.var 0)) 2 (ctrlBlocks l₀ l₁) := by
  refine congrArg (Region.cfg _ 2) (funext fun i => ?_)
  match i with
  | 0 => rfl
  | 1 => rfl

theorem ctrlArm_typed (l : Bool) : ValueBranches [Ty.unit, Bit, Bit] (ctrlArm l) [Bit, Bit, Bit] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 1) rfl)) (.br (ℓ := 2) (A := Bit) rfl (.var (i := 3) rfl))
    (.br (ℓ := 1) (A := Bit) rfl (.var (i := 0) rfl))

theorem ctrlHead_typed (l₀ l₁ : Bool) : ValueBranches [Bit, Bit] (ctrlHead l₀ l₁) [Bit, Bit, Bit] :=
  .case (A := Ty.unit) (B := Ty.unit) (.var (i := 1) rfl) (ctrlArm_typed l₀) (ctrlArm_typed l₁)

theorem ctrlBlocks_typed (l₀ l₁ : Bool) (i : Fin 2) :
    ValueBranches [Bit, Bit] (ctrlBlocks l₀ l₁ i) (List.ofFn (fun _ : Fin 2 => Bit) ++ [Bit]) :=
  match i with
  | 0 => ctrlHead_typed l₀ l₁
  | 1 => (ValueBranches.br (ℓ := 0) (A := Bit) (L := [Bit, Bit, Bit]) rfl (.var (i := 0) rfl)).renameVars
      (headerRen (S := Bit))

/-- The source is a guarded table at the entry `Bit` with exit `Bit`. -/
theorem ctrlSource_typed (l₀ l₁ : Bool) : ValueBranches [Bit] (ctrlSource l₀ l₁) [Bit] :=
  ctrlSource_eq l₀ l₁ ▸ .cfg (fun _ : Fin 2 => Bit) captEntry_typed (ctrlBlocks_typed l₀ l₁)

/-- The router table: row `c` sends the label `pickLabel l₀ l₁ c` and
stays in its row. -/
def ctrlRouter (l₀ l₁ : Bool) : Router 1 :=
  Router.ofLabels (fun i => pickLabel l₀ l₁ (pairBit i)) captAct

/-- One arm of the step on the pair, under the unit payload of the case
on the captured input. -/
def ctrlBodyArm (l : Bool) : Region signature.Instr :=
  .case (.op (.ask l) (.var 1)) (.br 0 (.inl (.var 3))) (.br 0 (.inr (.pair (.var 3) (.var 0))))

/-- The step on the pair `(c, y)`: case on `c` to choose the request,
send it with `y`; on the left reply return `c`; on the right reply `r`
repeat with `(c, r)`. -/
def ctrlBody (l₀ l₁ : Bool) : Region signature.Instr :=
  .let₂ (.var 0) (.case (.var 1) (ctrlBodyArm l₀) (ctrlBodyArm l₁))

theorem ctrlBodyArm_typed (l : Bool) :
    ValueBranches [Ty.unit, Bit, Bit, Pair] (ctrlBodyArm l) [Silmaril.coprod Bit Pair] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 1) rfl)) (.br rfl (.inl (.var (i := 3) rfl)))
    (.br rfl (.inr (.pair (.var (i := 3) rfl) (.var (i := 0) rfl))))

theorem ctrlBody_typed (l₀ l₁ : Bool) :
    ValueBranches [Pair] (ctrlBody l₀ l₁) [Silmaril.coprod Bit Pair] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Ty.unit) (B := Ty.unit) (.var (i := 1) rfl) (ctrlBodyArm_typed l₀) (ctrlBodyArm_typed l₁))

/-- The loop on the pair, entered with the input in both places. -/
def ctrlLoop (l₀ l₁ : Bool) : Region signature.Instr :=
  seqRegion dupEntry (loopRegion Pair (ctrlBody l₀ l₁))

theorem ctrlLoop_typed (l₀ l₁ : Bool) : ValueBranches [Bit] (ctrlLoop l₀ l₁) [Bit] :=
  seqRegion_typed dupEntry_typed (loopRegion_typed (ctrlBody_typed l₀ l₁))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
