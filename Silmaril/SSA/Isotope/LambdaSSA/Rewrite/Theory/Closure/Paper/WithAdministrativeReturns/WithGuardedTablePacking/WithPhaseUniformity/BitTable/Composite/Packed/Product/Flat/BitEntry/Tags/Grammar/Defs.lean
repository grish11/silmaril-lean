module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Cycle.Defs

/-! # The request and reply grammar with any number of blocks

`NTable K` is the data of a table with `K + 1` blocks:

* each block has one Bit parameter and sends one request with its own
  label, querying its parameter;
* each of the two replies is an `NLeaf K`: leave with the reply payload,
  or jump to a block with the reply payload;
* the entry jumps to the block `start` with the input.

From one value `d`: the table `d.source` with its blocks `d.blocks`, the
scoped flat graph `d.flat`, the capture-free rows `d.free` on the tags,
and the router table `d.router`.

`tagsFold` folds one region for each block into an arrow out of the tags,
and `toStatesN K` is the map from the tags of `K + 1` blocks to the states
of `K + 1` rows that sends each tag to its row.

`Task.nStep d` is the step equation of every row of `d`. It is the one
field of the certificate of `d` that is not proved for every size.
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
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion sumIso)

variable {K : Nat}

/-! ## Folding the tags -/

/-- One region for each block, folded into an arrow out of the tags. -/
noncomputable def tagsFold : (L : LCtx (Ty Empty)) → {E : Ty Empty} → FreeRows L E →
    (ofType (Φ := signature.Instr) (packedExitType L) ⟶ ofType E)
  | [], _, _ => (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to _
  | A :: L, _, β =>
    (sumIso (Φ := signature.Instr) A (packedExitType L)).hom ≫
      coprod.desc (ofRegion (β (i := 0) (A := A) rfl).property)
        (tagsFold L (fun i B h => β (i := i + 1) (A := B) h))

/-- From the tags of `K + 1` blocks to the states of `K + 1` rows. -/
noncomputable def toStatesN (K : Nat) : ofType (Φ := signature.Instr) (BitTags K) ⟶ ofType (States K) :=
  tagsFold _ (freeOfBlocks (fun i => .br 0 (injTm K i (.inl (.var 0)))) (rowState_typed (K := K)))

/-! ## The grammar -/

/-- A reply branch: leave with the reply payload, or jump to a block. -/
inductive NLeaf (K : Nat)
  | exit
  | goto (j : Fin (K + 1))

namespace NLeaf

/-- The label of a leaf: the blocks first, then the exit. -/
def fin : NLeaf K → Fin (K + 1 + 1)
  | .exit => Fin.last (K + 1)
  | .goto j => j.castSucc

def idx (b : NLeaf K) : Nat := b.fin.val

/-- The router action of a leaf on a reply payload. -/
def toAct : NLeaf K → Bool → Act K
  | .exit, pl => .ret pl
  | .goto j, pl => .go j pl

/-- The leaf with its exit tagged: return the payload, or continue at the
tag of a block. -/
def free : NLeaf K → Region signature.Instr
  | .exit => .br 0 (.inl (.var 0))
  | .goto j => .br 0 (.inr (packedExitArg j.val (.var 0)))

end NLeaf

/-- The data of a table with `K + 1` blocks. -/
structure NTable (K : Nat) where
  label : Fin (K + 1) → Bool
  branch : Fin (K + 1) → Bool → NLeaf K
  start : Fin (K + 1)

theorem atBlock (j : Fin (K + 1)) : At (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit]) j.val Bit :=
  (List.getElem?_append_left (by simp)).trans (atBit j)

theorem atExit : At (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit]) (K + 1) Bit := by
  simp [At]

theorem nleaf_typed {Γ : VCtx (Ty Empty)} :
    (b : NLeaf K) → ValueBranches (Bit :: Γ) (.br b.idx (.var 0) : Region signature.Instr)
      (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit])
  | .exit => .br (ℓ := K + 1) (A := Bit) atExit (.var (i := 0) rfl)
  | .goto j => .br (ℓ := j.val) (A := Bit) (atBlock j) (.var (i := 0) rfl)

/-- The tag of a block as a value, in any context. -/
theorem bitTag_value {Γ : VCtx (Ty Empty)} (j : Fin (K + 1)) :
    Tm.BranchValue (Bit :: Γ) (packedExitArg j.val (.var 0) : Tm signature.Instr) (BitTags K) := by
  cases packExits_valueFamily (Φ := signature.Instr) Γ _ (atBit j) with
  | br ho hv =>
    cases Option.some.inj ho
    exact hv

theorem nleaf_free_typed {Γ : VCtx (Ty Empty)} :
    (b : NLeaf K) → ValueBranches (Bit :: Γ) b.free [Silmaril.coprod Bit (BitTags K)]
  | .exit => .br rfl (.inl (.var (i := 0) rfl))
  | .goto j => .br rfl (.inr (bitTag_value j))

namespace NTable

variable (d : NTable K)

/-- A block: one request on the parameter, and a jump with the payload on
each reply. -/
def blocks (i : Fin (K + 1)) : Region signature.Instr :=
  .case (.op (.ask (d.label i)) (.var 0)) (.br (d.branch i false).idx (.var 0))
    (.br (d.branch i true).idx (.var 0))

/-- The table. -/
def source : Region signature.Instr := .cfg (.br d.start.val (.var 0)) (K + 1) d.blocks

/-- The scoped flat graph. -/
def flat : LambdaSSA.FiniteCFG signature.Instr (K + 1) 1 1 where
  entry := .br d.start.castSucc (.bv 0)
  block := fun i => .case (.op (.ask (d.label i)) (.bv 0)) (.br (d.branch i false).fin (.bv 0))
    (.br (d.branch i true).fin (.bv 0))

/-- The region of the flat graph is the table. -/
theorem flat_erase : d.flat.erase = d.source := rfl

theorem entry_typed :
    ValueBranches [Bit] (.br d.start.val (.var 0) : Region signature.Instr)
      (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit]) :=
  .br (ℓ := d.start.val) (A := Bit) (atBlock d.start) (.var (i := 0) rfl)

theorem blocks_typed (i : Fin (K + 1)) :
    ValueBranches [Bit, Bit] (d.blocks i) (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit]) :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (nleaf_typed _) (nleaf_typed _)

/-- The table is a guarded source at the entry `Bit` with exit `Bit`. -/
theorem source_typed : ValueBranches [Bit] d.source [Bit] :=
  .cfg (fun _ : Fin (K + 1) => Bit) d.entry_typed d.blocks_typed

/-- The capture-free row of a block. -/
def free (i : Fin (K + 1)) : Region signature.Instr :=
  .case (.op (.ask (d.label i)) (.var 0)) (d.branch i false).free (d.branch i true).free

theorem free_typed (i : Fin (K + 1)) :
    ValueBranches [Bit] (d.free i) [Silmaril.coprod Bit (BitTags K)] :=
  .case (A := Bit) (B := Bit) (.op (.var (i := 0) rfl)) (nleaf_free_typed _) (nleaf_free_typed _)

/-- The router table. -/
def act (i : Fin (K + 1)) (tag pl : Bool) : Act K :=
  match tag with
  | false => (d.branch i false).toAct pl
  | true => (d.branch i true).toAct pl

def router : Router K := Router.ofLabels d.label d.act

end NTable

/-- The step equation of every row: the capture-free row, with its tags
sent to states, is the row of the router table. -/
def Task.nStep (d : NTable K) : Prop :=
  ∀ i, ofRegion (d.free_typed i) ≫
      ((sumIso (Φ := signature.Instr) Bit (BitTags K)).hom ≫ coprod.map (𝟙 _) (toStatesN K)) =
    (ofRegion bitState_typed ≫ ofRegion (d.router.rows_typed i)) ≫
      (sumIso (Φ := signature.Instr) Bit (States K)).hom

/-- The cycle of three blocks, as a table of the grammar. -/
def cycleN (l : Bool) : NTable 2 where
  label := fun _ => l
  branch := fun i tag => match tag with
    | false => .exit
    | true => .goto (cycNext i)
  start := 0

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
