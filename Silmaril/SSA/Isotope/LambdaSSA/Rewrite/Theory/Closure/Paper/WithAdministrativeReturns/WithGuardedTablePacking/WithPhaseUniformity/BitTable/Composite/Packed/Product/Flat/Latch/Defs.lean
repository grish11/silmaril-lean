module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms

/-! # A cyclic flat source with a header and a separate back-edge block

The two-Bit loop is split into two blocks. Neither block uses the
captured input.

* `latchNamed l` is a named cyclic table. The block `head` receives a
  pair `s`, binds its Bits `x` and `y`, and sends the request `l` with
  `y`. On the left reply it jumps to the exit with `x`. On the right
  reply `r` it jumps to the block `latch` with `(r, x)`. The block
  `latch` has its own parameter `t` and jumps back to `head` with it.
* `latchFlat l` is the scoped flat graph with two blocks, one exit and one
  captured input: label `0` is the header, label `1` the back-edge block
  and label `2` the exit.
* `latchSource l` is its region: a guarded table with two blocks.
* `twoRows` is the dispatcher of two rows on a captured input as the
  packed readback writes it, and `freeStep` the step of two rows on the
  tags alone.
* `headRow`, `latchRow` are the rows of the readback of this source, and
  `headStep`, `latchStep` the same blocks as steps on their parameters.
* `latchReadback l` is its packed readback, the right side of the
  table-packing seed. Its loop state is `LatchState`, the captured input
  paired with the tagged parameters of the two blocks.
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

open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.Retained (distributorRegion)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion sumIso)

/-! ## A dispatcher of two rows on a captured input -/

/-- Distribute the captured input over the sum exit of a step, and drop
it on the return side. -/
def dropCase : Region signature.Instr :=
  .let₂ (.var 0) (.case (.var 0) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.pair (.var 2) (.var 0)))))

theorem dropCase_typed {X B A : Ty Empty} :
    ValueBranches [Silmaril.product X (Silmaril.coprod B A)] dropCase
      [Silmaril.coprod B (Silmaril.product X A)] :=
  .let₂ (A := X) (B := Silmaril.coprod B A) (.var rfl)
    (.case (A := B) (B := A) (.var rfl) (.br rfl (.inl (.var rfl)))
      (.br rfl (.inr (.pair (.var rfl) (.var rfl)))))

/-- The dispatcher of two rows on a captured input, as the packed
readback writes it: distribute the input over the tags and run the
selected row. `dR` is the row of the empty tail. -/
def twoRows (ρ₀ ρ₁ dR : Region signature.Instr) : Region signature.Instr :=
  seqRegion distributorRegion (.case (.var 0) (ρ₀.renameVars (lift Nat.succ))
    ((seqRegion distributorRegion (.case (.var 0) (ρ₁.renameVars (lift Nat.succ))
      ((seqRegion (.let₂ (.var 0) (.br 0 (.var 0))) dR).renameVars (lift Nat.succ)))).renameVars
        (lift Nat.succ)))

/-- The step of two rows that do not see the captured input, on the tags
alone: the first row, the second row, and the empty tail. -/
noncomputable def freeStep {A₀ A₁ D : Ty Empty} {β₀ β₁ : Region signature.Instr}
    (hβ₀ : ValueBranches [A₀] β₀
      [Silmaril.coprod D (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))])
    (hβ₁ : ValueBranches [A₁] β₁
      [Silmaril.coprod D (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))]) :
    ofType (Φ := signature.Instr) (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)) ⟶
      ofType D ⨿ ofType (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty)) :=
  (sumIso (Φ := signature.Instr) A₀ (Silmaril.coprod A₁ Silmaril.empty)).hom ≫
    coprod.desc (ofRegion hβ₀ ≫ (sumIso (Φ := signature.Instr) D
        (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))).hom)
      ((sumIso (Φ := signature.Instr) A₁ Silmaril.empty).hom ≫
        coprod.desc (ofRegion hβ₁ ≫ (sumIso (Φ := signature.Instr) D
            (Silmaril.coprod A₀ (Silmaril.coprod A₁ Silmaril.empty))).hom)
          ((Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to _))

/-! ## The two-block source -/

/-- Labels of the named two-block source. -/
inductive LatchLabel
  | head | latch | exit
  deriving DecidableEq

/-- Registers of the named two-block source. -/
inductive LatchReg
  | p | s | x | y | r | t
  deriving DecidableEq

/-- The named cyclic source: `head (s): (x, y) = s; case ask l y of
r ⇒ exit x | r ⇒ latch (r, x)` and `latch (t): head t`, entered with
`head p`. -/
def latchNamed (l : Bool) : Silmaril.SSA.LambdaRTL.CFG LatchReg LatchLabel signature.Instr where
  entry := .term (.br .head (.var .p))
  blocks := [(.head, ⟨.s, .let2 .x .y (.val (.var .s))
      (.term (.case (.app (.ask l) (.var .y)) .r (.br .exit (.var .x))
        .r (.br .latch (.pair (.var .r) (.var .x)))))⟩),
    (.latch, ⟨.t, .term (.br .head (.var .t))⟩)]

/-- The scoped flat graph: the header at label `0`, the back-edge block
at label `1`, the exit at label `2`, and the input as the one captured
variable. -/
def latchFlat (l : Bool) : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br 0 (.bv 0)
  block := fun i => match i with
    | 0 => .let₂ (.bv 0) (.case (.op (.ask l) (.bv 0)) (.br 2 (.bv 2)) (.br 1 (.pair (.bv 0) (.bv 2))))
    | 1 => .br 0 (.bv 0)

/-- The header block as a region on its parameter: label `1` is the
back-edge block and label `2` the exit. -/
def headBlock (l : Bool) : Region signature.Instr :=
  .let₂ (.var 0) (.case (.op (.ask l) (.var 0)) (.br 2 (.var 2)) (.br 1 (.pair (.var 0) (.var 2))))

/-- The back-edge block as a region on its parameter: it jumps to the
header at label `0`. -/
def latchBlock : Region signature.Instr := .br 0 (.var 0)

/-- The blocks of the table. Neither uses the captured input. -/
def latchBlocks (l : Bool) (i : Fin 2) : Region signature.Instr :=
  match i with
  | 0 => (headBlock l).renameVars (lift Nat.succ)
  | 1 => latchBlock.renameVars (lift Nat.succ)

/-- The region of the two-block flat source. -/
def latchSource (l : Bool) : Region signature.Instr := (latchFlat l).erase

/-- The source is the table of the two capture-free blocks. -/
theorem latchSource_eq (l : Bool) : latchSource l = .cfg (.br 0 (.var 0)) 2 (latchBlocks l) := by
  refine congrArg (Region.cfg _ 2) (funext fun i => ?_)
  match i with
  | 0 => rfl
  | 1 => rfl

theorem latchEntry_typed :
    ValueBranches [Pair] (.br 0 (.var 0) : Region signature.Instr)
      (List.ofFn (fun _ : Fin 2 => Pair) ++ [Bit]) :=
  .br (ℓ := 0) (A := Pair) rfl (.var rfl)

theorem headBlock_typed (l : Bool) : ValueBranches [Pair] (headBlock l) [Pair, Pair, Bit] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br (ℓ := 2) (A := Bit) rfl (.var rfl))
      (.br (ℓ := 1) (A := Pair) rfl (.pair (.var rfl) (.var rfl))))

theorem latchBlock_typed : ValueBranches [Pair] (latchBlock : Region signature.Instr) [Pair, Pair, Bit] :=
  .br (ℓ := 0) (A := Pair) rfl (.var rfl)

theorem latchBlocks_typed (l : Bool) (i : Fin 2) :
    ValueBranches [Pair, Pair] (latchBlocks l i) (List.ofFn (fun _ : Fin 2 => Pair) ++ [Bit]) :=
  match i with
  | 0 => (headBlock_typed l).renameVars headerRen
  | 1 => latchBlock_typed.renameVars headerRen

/-- The tagged parameters of the two blocks. -/
abbrev LatchTags : Ty Empty := packedExitType [Pair, Pair]

/-- The state of the readback loop: the captured input paired with the
tagged parameters of the two blocks. -/
abbrev LatchState : Ty Empty := Silmaril.product Pair LatchTags

/-- The source is a guarded table at the entry `Pair` with exit `Bit`. -/
theorem latchSource_typed (l : Bool) : ValueBranches [Pair] (latchSource l) [Bit] :=
  latchSource_eq l ▸ .cfg (fun _ : Fin 2 => Pair) latchEntry_typed (latchBlocks_typed l)

/-- The packed readback of the two-block table. -/
noncomputable def latchReadback (l : Bool) : {r : Region signature.Instr // ValueBranches [Pair] r [Bit]} :=
  packedReadbackRep (fun _ : Fin 2 => Pair) latchEntry_typed (latchBlocks_typed l)

/-! ## The rows of the readback and the capture-free steps -/

/-- The row of the header in the packed readback: it unpacks the captured
input and the parameter, and pairs the captured input with the tagged
parameter of the back-edge block. -/
def headRow (l : Bool) : Region signature.Instr :=
  .let₂ (.var 0) (.let₂ (.var 0) (.case (.op (.ask l) (.var 0)) (.br 0 (.inl (.var 2)))
    (.br 0 (.inr (.pair (.var 4) (.inr (.inl (.pair (.var 0) (.var 2)))))))))

/-- The row of the back-edge block in the packed readback. -/
def latchRow : Region signature.Instr :=
  .let₂ (.var 0) (.br 0 (.inr (.pair (.var 1) (.inl (.var 0)))))

/-- The header as a step on its parameter alone: return the first Bit, or
continue at the tag of the back-edge block. -/
def headStep (l : Bool) : Region signature.Instr :=
  .let₂ (.var 0) (.case (.op (.ask l) (.var 0)) (.br 0 (.inl (.var 2)))
    (.br 0 (.inr (.inr (.inl (.pair (.var 0) (.var 2)))))))

/-- The back-edge block as a step on its parameter alone: continue at
the tag of the header. -/
def latchStep : Region signature.Instr := .br 0 (.inr (.inl (.var 0)))

/-- Enter the tags at the header. -/
theorem tagHead_typed :
    ValueBranches [Pair] (.br 0 (.inl (.var 0)) : Region signature.Instr) [LatchTags] :=
  .br rfl (.inl (.var rfl))

theorem headRow_typed (l : Bool) :
    ValueBranches [Silmaril.product Pair Pair] (headRow l) [Silmaril.coprod Bit LatchState] :=
  .let₂ (A := Pair) (B := Pair) (.var rfl) (.let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var rfl)))
      (.br rfl (.inr (.pair (.var rfl) (.inr (.inl (.pair (.var rfl) (.var rfl)))))))))

theorem latchRow_typed :
    ValueBranches [Silmaril.product Pair Pair] (latchRow : Region signature.Instr)
      [Silmaril.coprod Bit LatchState] :=
  .let₂ (A := Pair) (B := Pair) (.var rfl) (.br rfl (.inr (.pair (.var rfl) (.inl (.var rfl)))))

theorem headStep_typed (l : Bool) : ValueBranches [Pair] (headStep l) [Silmaril.coprod Bit LatchTags] :=
  .let₂ (A := Bit) (B := Bit) (.var rfl)
    (.case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (.br rfl (.inl (.var rfl)))
      (.br rfl (.inr (.inr (.inl (.pair (.var rfl) (.var rfl)))))))

theorem latchStep_typed :
    ValueBranches [Pair] (latchStep : Region signature.Instr) [Silmaril.coprod Bit LatchTags] :=
  .br rfl (.inr (.inl (.var rfl)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
