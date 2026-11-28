module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Defs

/-! # A cyclic flat source with two live Bits at its loop header

The source is written in the flat layers of the library, not read back
from `pairBody`.

* `pairNamed l` is a named cyclic table (`LambdaRTL.CFG`) with registers
  and labels. Its entry jumps to `head` with the input `p`. The block
  `head` receives a pair `s`, binds its two Bits `x` and `y`, and sends
  the request `l` with `y`. On the left reply it jumps to the exit with
  `x`. On the right reply `r` it jumps back to `head` with `(r, x)`.
* `pairFlat l` is the scoped flat graph (`LambdaSSA.FiniteCFG`) with one
  block, one exit and one captured input: label `0` is the header and
  label `1` the exit.
* `pairSource l` is its region: a guarded table with a back edge.
* `flatLoop b` is the general one-header table with header block `b`,
  entered at the header with the input. `flatStep b` reads the two labels
  of `b` as the sum exit of a loop step.
* `pairReadback l` is the packed readback of that table, the right side
  of the table-packing seed. `ReadbackState` is the state of its loop.
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

variable {S : Ty Empty} {b : Region signature.Instr}

/-! ## One-header flat loops -/

/-- Read the two labels of a header block as the sum exit of a loop
step: the back edge `0` repeats and the exit `1` returns. -/
def sumExits : Nat → Region signature.Instr
  | 0 => .br 0 (.inr (.var 0))
  | _ + 1 => .br 0 (.inl (.var 0))

theorem sumExits_typed {Γ : VCtx (Ty Empty)} :
    LSubst.ValueFamily Γ [S, Bit] [Silmaril.coprod Bit S] sumExits
  | 0, _, h => by
    cases h
    exact .br (ℓ := 0) rfl (.inr (.var rfl))
  | 1, _, h => by
    cases h
    exact .br (ℓ := 0) rfl (.inl (.var rfl))

/-- The loop step of a header block: its back edge and its exit are
tagged into one sum exit. -/
def flatStep (b : Region signature.Instr) : Region signature.Instr := b.lsubst sumExits

theorem flatStep_typed (hb : ValueBranches [S] b [S, Bit]) :
    ValueBranches [S] (flatStep b) [Silmaril.coprod Bit S] :=
  hb.lsubst sumExits_typed

/-- The flat table with the one header block `b`, entered at the header
with the input. The block does not use the captured input. -/
def flatLoop (b : Region signature.Instr) : Region signature.Instr :=
  .cfg (.br 0 (.var 0)) 1 (fun _ => b.renameVars (lift Nat.succ))

theorem headerRen : Ren [S] [S, S] (lift Nat.succ)
  | 0, _, h => h

theorem flatLoop_typed (hb : ValueBranches [S] b [S, Bit]) : ValueBranches [S] (flatLoop b) [Bit] :=
  .cfg (fun _ : Fin 1 => S) (.br (ℓ := 0) (A := S) rfl (.var rfl)) (fun _ => hb.renameVars headerRen)

/-! ## The source with two live Bits -/

/-- Registers of the named source. -/
inductive PairReg
  | p | s | x | y | r
  deriving DecidableEq

/-- Labels of the named source. -/
inductive PairLabel
  | head | exit
  deriving DecidableEq

/-- The named cyclic source: `head (s): (x, y) = s; case ask l y of
r ⇒ exit x | r ⇒ head (r, x)`, entered with `head p`. -/
def pairNamed (l : Bool) : Silmaril.SSA.LambdaRTL.CFG PairReg PairLabel signature.Instr where
  entry := .term (.br .head (.var .p))
  blocks := [(.head, ⟨.s, .let2 .x .y (.val (.var .s))
    (.term (.case (.app (.ask l) (.var .y)) .r (.br .exit (.var .x))
      .r (.br .head (.pair (.var .r) (.var .x)))))⟩)]

/-- The scoped flat graph: one header block with the back edge at label
`0`, one exit at label `1`, and the input as the one captured variable. -/
def pairFlat (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 1 1 1 where
  entry := .br 0 (.bv 0)
  block := fun _ => .let₂ (.bv 0)
    (.case (.op (.ask l) (.bv 0)) (.br 1 (.bv 2)) (.br 0 (.pair (.bv 0) (.bv 2))))

/-- The header block as a region. Label `0` is the back edge and label
`1` the exit. -/
def flatBlock (l : Bool) : Region signature.Instr :=
  .let₂ (.var 0) (.case (.op (.ask l) (.var 0)) (.br 1 (.var 2)) (.br 0 (.pair (.var 0) (.var 2))))

/-- The region of the flat source. -/
def pairSource (l : Bool) : Region signature.Instr := (pairFlat l).erase

/-- The source is the one-header table of its header block. -/
theorem pairSource_eq (l : Bool) : pairSource l = flatLoop (flatBlock l) := rfl

/-- The loop step of the header block is the step written on pairs. -/
theorem flatStep_flatBlock (l : Bool) : flatStep (flatBlock l) = pairBody l := rfl

theorem flatBody_typed (l : Bool) : ValueBranches [Pair] (flatBlock l) [Pair, Bit] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br (ℓ := 1) (A := Bit) rfl (.var rfl))
      (.br (ℓ := 0) (A := Pair) rfl (.pair (.var rfl) (.var rfl))))

theorem flatEntry_typed :
    ValueBranches [Pair] (.br 0 (.var 0) : Region signature.Instr)
      (List.ofFn (fun _ : Fin 1 => Pair) ++ [Bit]) :=
  .br (ℓ := 0) (A := Pair) rfl (.var rfl)

theorem flatBlock_typed (l : Bool) (_ : Fin 1) :
    ValueBranches [Pair, Pair] (flatBlock l) (List.ofFn (fun _ : Fin 1 => Pair) ++ [Bit]) :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br (ℓ := 1) (A := Bit) rfl (.var rfl))
      (.br (ℓ := 0) (A := Pair) rfl (.pair (.var rfl) (.var rfl))))

/-- The source is a guarded table at the entry `Pair` with exit `Bit`. -/
theorem pairSource_typed (l : Bool) : ValueBranches [Pair] (pairSource l) [Bit] :=
  .cfg (fun _ : Fin 1 => Pair) flatEntry_typed (flatBlock_typed l)

/-- The packed readback of the source table. -/
noncomputable def pairReadback (l : Bool) : {r : Region signature.Instr // ValueBranches [Pair] r [Bit]} :=
  packedReadbackRep (fun _ : Fin 1 => Pair) flatEntry_typed (flatBlock_typed l)

/-- The state of the readback loop: the captured input paired with the
tagged parameter of the header. -/
abbrev ReadbackState : Ty Empty := Silmaril.product Pair (packedExitType [Pair])

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
