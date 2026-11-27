module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Defs

/-! # A reified fragment of cyclic flat sources: two polling blocks

`PollTable` is the data of a flat source in a delimited fragment:

* two blocks, indexed by a Bit, each with one Bit parameter;
* each block sends one request, with its label, querying its parameter;
* each of the two replies is a `PollLeaf`: leave with the reply payload
  (`exit`), or jump to a block with the reply payload (`goto c`);
* the entry jumps to the block `start` with the input.

No block uses the captured input, and there is no request-free block.

From the same data:

* `PollTable.flat` is the scoped flat graph, and `PollTable.source` its
  region;
* `PollTable.router` is the router table: row `c` has the label of block
  `c`, a `exit` reply returns the payload, and a `goto c'` reply
  continues at row `c'` with the payload.
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

/-- A reply branch of a block: leave with the reply payload, or jump to a
block with the reply payload. -/
inductive PollLeaf
  | exit
  | goto (c : Bool)

/-- The label of a leaf in the graph: blocks first, then the exit. -/
def PollLeaf.fin : PollLeaf → Fin 3
  | .exit => 2
  | .goto false => 0
  | .goto true => 1

def PollLeaf.idx (b : PollLeaf) : Nat := b.fin.val

/-- The router action of a leaf on a reply payload. -/
def PollLeaf.toAct : PollLeaf → Bool → Act 1
  | .exit, pl => .ret pl
  | .goto c, pl => .go (pairIdx c) pl

/-- The four actions of a block from its two leaves. -/
def leafAct (b₁ b₂ : PollLeaf) (tag pl : Bool) : Act 1 :=
  match tag with
  | false => b₁.toAct pl
  | true => b₂.toAct pl

/-- The data of a source in the fragment. -/
structure PollTable where
  label : Bool → Bool
  branch : Bool → Bool → PollLeaf
  start : Bool

/-- The label of the start block in the graph. -/
def startFin (s : Bool) : Fin 3 :=
  match s with
  | false => 0
  | true => 1

/-- A block in scoped flat syntax: one request with the parameter, and a
jump with the payload on each reply. -/
def pollFlatBlock (l : Bool) (b₁ b₂ : PollLeaf) : LambdaSSA.Flat signature.Instr 3 2 :=
  .case (.op (.ask l) (.bv 0)) (.br b₁.fin (.bv 0)) (.br b₂.fin (.bv 0))

/-- The same block as a region. -/
def pollBlock (l : Bool) (b₁ b₂ : PollLeaf) : Region signature.Instr :=
  .case (.op (.ask l) (.var 0)) (.br b₁.idx (.var 0)) (.br b₂.idx (.var 0))

namespace PollTable

variable (d : PollTable)

/-- The scoped flat graph of the data. -/
def flat : LambdaSSA.FiniteCFG signature.Instr 2 1 1 where
  entry := .br (startFin d.start) (.bv 0)
  block := fun i => pollFlatBlock (d.label (pairBit i)) (d.branch (pairBit i) false) (d.branch (pairBit i) true)

def blocks (i : Fin 2) : Region signature.Instr :=
  pollBlock (d.label (pairBit i)) (d.branch (pairBit i) false) (d.branch (pairBit i) true)

/-- The region of the flat graph. -/
def source : Region signature.Instr := d.flat.erase

theorem source_eq : d.source = .cfg (.br (startFin d.start).val (.var 0)) 2 d.blocks := rfl

/-- The router table of the data. -/
def act (i : Fin 2) : Bool → Bool → Act 1 :=
  leafAct (d.branch (pairBit i) false) (d.branch (pairBit i) true)

def router : Router 1 := Router.ofLabels (fun i => d.label (pairBit i)) d.act

end PollTable

theorem pollLeaf_typed {Γ : VCtx (Ty Empty)} :
    (b : PollLeaf) → ValueBranches (Bit :: Γ) (.br b.idx (.var 0) : Region signature.Instr) [Bit, Bit, Bit]
  | .exit => .br (ℓ := 2) (A := Bit) rfl (.var rfl)
  | .goto false => .br (ℓ := 0) (A := Bit) rfl (.var rfl)
  | .goto true => .br (ℓ := 1) (A := Bit) rfl (.var rfl)

theorem pollBlock_typed {Γ : VCtx (Ty Empty)} (l : Bool) (b₁ b₂ : PollLeaf) :
    ValueBranches (Bit :: Γ) (pollBlock l b₁ b₂) [Bit, Bit, Bit] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (pollLeaf_typed b₁) (pollLeaf_typed b₂)

theorem startEntry_typed :
    (s : Bool) → ValueBranches [Bit] (.br (startFin s).val (.var 0) : Region signature.Instr)
      (List.ofFn (fun _ : Fin 2 => Bit) ++ [Bit])
  | false => .br (ℓ := 0) (A := Bit) rfl (.var rfl)
  | true => .br (ℓ := 1) (A := Bit) rfl (.var rfl)

namespace PollTable

variable (d : PollTable)

theorem blocks_typed (i : Fin 2) :
    ValueBranches [Bit, Bit] (d.blocks i) (List.ofFn (fun _ : Fin 2 => Bit) ++ [Bit]) :=
  pollBlock_typed _ _ _

/-- The source is a guarded table at the entry `Bit` with exit `Bit`. -/
theorem source_typed : ValueBranches [Bit] d.source [Bit] :=
  d.source_eq ▸ .cfg (fun _ : Fin 2 => Bit) (startEntry_typed d.start) d.blocks_typed

/-- The packed readback of the source table. -/
noncomputable def readback : {r : Region signature.Instr // ValueBranches [Bit] r [Bit]} :=
  packedReadbackRep (fun _ : Fin 2 => Bit) (startEntry_typed d.start) d.blocks_typed

end PollTable

/-! ## Three tables -/

/-- Each block leaves on the left reply and repeats itself on the right. -/
def selfTable (l : Bool) : PollTable where
  label := fun _ => l
  branch := fun c tag => match tag with
    | false => .exit
    | true => .goto c
  start := false

/-- Each block leaves on the left reply and goes to the other block on
the right. -/
def swapTable (l : Bool) : PollTable where
  label := fun _ => l
  branch := fun c tag => match tag with
    | false => .exit
    | true => .goto (!c)
  start := false

/-- No block ever leaves. -/
def neverTable (l : Bool) : PollTable where
  label := fun _ => l
  branch := fun c _ => .goto c
  start := false

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
