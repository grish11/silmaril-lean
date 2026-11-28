module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Defs

/-! # A cycle of three polling blocks

`cycleFlat l` is a scoped flat graph with three blocks, one exit and one
captured input. Block `i` sends the request `l` with its parameter. On
the left reply it leaves with the reply payload. On the right reply it
jumps to block `i + 1`, and the last block jumps to the first. The entry
jumps to block `0` with the input.

`cycleRouter l` is the router table with three rows of the same shape.
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

/-- The next block of the cycle. -/
def cycNext (i : Fin 3) : Fin 3 :=
  match i with
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- The scoped flat graph of the cycle: blocks at labels `0`, `1`, `2`
and the exit at label `3`. -/
def cycleFlat (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 3 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .case (.op (.ask l) (.bv 0)) (.br 3 (.bv 0)) (.br 1 (.bv 0))
    | 1 => .case (.op (.ask l) (.bv 0)) (.br 3 (.bv 0)) (.br 2 (.bv 0))
    | 2 => .case (.op (.ask l) (.bv 0)) (.br 3 (.bv 0)) (.br 0 (.bv 0))

/-- A block of the cycle as a region. -/
def cycleBlocks (l : Bool) (i : Fin 3) : Region signature.Instr :=
  .case (.op (.ask l) (.var 0)) (.br 3 (.var 0)) (.br (cycNext i).val (.var 0))

/-- The region of the cycle. -/
def cycleSource (l : Bool) : Region signature.Instr := (cycleFlat l).erase

theorem cycleSource_eq (l : Bool) : cycleSource l = .cfg (.br 0 (.var 0)) 3 (cycleBlocks l) := by
  refine congrArg (Region.cfg _ 3) (funext fun i => ?_)
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl

theorem cycleEntry_typed :
    ValueBranches [Bit] (.br 0 (.var 0) : Region signature.Instr)
      (List.ofFn (fun _ : Fin 3 => Bit) ++ [Bit]) :=
  .br (ℓ := 0) (A := Bit) rfl (.var rfl)

theorem cycLeaf_typed {Γ : VCtx (Ty Empty)} (j : Fin 4) :
    ValueBranches (Bit :: Γ) (.br j.val (.var 0) : Region signature.Instr) [Bit, Bit, Bit, Bit] :=
  match j with
  | 0 => .br (ℓ := 0) (A := Bit) rfl (.var (i := 0) rfl)
  | 1 => .br (ℓ := 1) (A := Bit) rfl (.var (i := 0) rfl)
  | 2 => .br (ℓ := 2) (A := Bit) rfl (.var (i := 0) rfl)
  | 3 => .br (ℓ := 3) (A := Bit) rfl (.var (i := 0) rfl)

theorem cycleBlocks_typed (l : Bool) (i : Fin 3) :
    ValueBranches [Bit, Bit] (cycleBlocks l i) (List.ofFn (fun _ : Fin 3 => Bit) ++ [Bit]) :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (cycLeaf_typed 3)
    (match i with
      | 0 => cycLeaf_typed 1
      | 1 => cycLeaf_typed 2
      | 2 => cycLeaf_typed 0)

/-- The source is a guarded table at the entry `Bit` with exit `Bit`. -/
theorem cycleSource_typed (l : Bool) : ValueBranches [Bit] (cycleSource l) [Bit] :=
  cycleSource_eq l ▸ .cfg (fun _ : Fin 3 => Bit) cycleEntry_typed (cycleBlocks_typed l)

/-- The router table of the cycle. -/
def cycleAct (i : Fin 3) (tag pl : Bool) : Act 2 :=
  match tag with
  | false => .ret pl
  | true => .go (cycNext i) pl

def cycleRouter (l : Bool) : Router 2 := Router.ofLabels (fun _ => l) cycleAct

/-- The capture-free row of a block: the request, then return the reply
payload or continue at the tag of the next block. -/
def cycleFree (l : Bool) (i : Fin 3) : Region signature.Instr :=
  .case (.op (.ask l) (.var 0)) (.br 0 (.inl (.var 0)))
    (.br 0 (.inr (packedExitArg (cycNext i).val (.var 0))))

theorem cycTag_value {Γ : VCtx (Ty Empty)} (j : Fin 3) :
    Tm.BranchValue (Bit :: Γ) (packedExitArg j.val (.var 0) : Tm signature.Instr) (BitTags 2) :=
  match j with
  | 0 => .inl (.var (i := 0) rfl)
  | 1 => .inr (.inl (.var (i := 0) rfl))
  | 2 => .inr (.inr (.inl (.var (i := 0) rfl)))

theorem cycleFree_typed (l : Bool) (i : Fin 3) :
    ValueBranches [Bit] (cycleFree l i) [Silmaril.coprod Bit (BitTags 2)] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var (i := 0) rfl)))
    (.br rfl (.inr (cycTag_value (cycNext i))))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
