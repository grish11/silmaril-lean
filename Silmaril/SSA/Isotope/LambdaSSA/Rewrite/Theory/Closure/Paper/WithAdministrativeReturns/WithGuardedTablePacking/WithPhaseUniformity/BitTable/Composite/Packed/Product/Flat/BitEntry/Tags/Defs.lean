module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.PollTable.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Tables with any number of blocks: tags, capture-free rows, certificates

The packed readback of a table with blocks of parameter types `L` loops
on the captured input paired with a tag: an element of
`packedExitType L`, one summand for each block and an empty tail.

* `tagAt_typed`: the tag of the block at a position of `L`.
* `FreeRows L E`: for each block, a region on its parameter alone.
* `freeDisp L β`: the step on the tags that runs the row of the tagged
  block. It is defined by recursion on `L`, for any list.

For a table of `K + 1` blocks with one Bit parameter each:

* `BitTags K` is the type of tags, `bitTag_typed i` the tag of block `i`;
* `freeOfBlocks` makes `FreeRows` from one region for each block;
* `TagCert` collects the checked facts that relate a table to a router
  table with `K + 1` rows.
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
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (whiskerLeftRegion whiskerLeftRegion_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (orderedRow entry_route)

/-! ## Any list of blocks -/

/-- The tag of the block at position `i`. -/
theorem tagAt_typed {L : LCtx (Ty Empty)} {i : Nat} {A : Ty Empty} (h : At L i A) :
    ValueBranches [A] (.br 0 (packedExitArg i (.var 0)) : Region signature.Instr) [packedExitType L] :=
  packExits_valueFamily [] L h

/-- A region on the parameter of each block, with one exit of type `E`. -/
abbrev FreeRows (L : LCtx (Ty Empty)) (E : Ty Empty) : Type :=
  ∀ ⦃i : Nat⦄ ⦃A : Ty Empty⦄, At L i A → {r : Region signature.Instr // ValueBranches [A] r [E]}

/-- The step on the tags: run the row of the tagged block. -/
noncomputable def freeDisp : (L : LCtx (Ty Empty)) → {D P : Ty Empty} → FreeRows L (Silmaril.coprod D P) →
    (ofType (Φ := signature.Instr) (packedExitType L) ⟶ ofType D ⨿ ofType P)
  | [], _, _, _ => (Paper.TypeCategory.emptyIsInitial (Φ := signature.Instr)).to _
  | A :: L, D, P, β =>
    (sumIso (Φ := signature.Instr) A (packedExitType L)).hom ≫
      coprod.desc (ofRegion (β (i := 0) (A := A) rfl).property ≫ (sumIso (Φ := signature.Instr) D P).hom)
        (freeDisp L (fun i B h => β (i := i + 1) (A := B) h))

/-- The position of a block in its list. -/
theorem atGet (L : LCtx (Ty Empty)) (i : Fin L.length) : At L i.val (L.get i) :=
  List.getElem?_eq_getElem i.isLt

/-! ## Blocks with one Bit parameter -/

variable {K : Nat}

/-- The tags of `K + 1` blocks with one Bit parameter each. -/
abbrev BitTags (K : Nat) : Ty Empty := packedExitType (List.ofFn (fun _ : Fin (K + 1) => Bit))

theorem atBit (i : Fin (K + 1)) : At (List.ofFn (fun _ : Fin (K + 1) => Bit)) i.val Bit :=
  SSA.FiniteSum.at_ofFn (fun _ : Fin (K + 1) => Bit) i

/-- The tag of block `i`. -/
theorem bitTag_typed (i : Fin (K + 1)) :
    ValueBranches [Bit] (.br 0 (packedExitArg i.val (.var 0)) : Region signature.Instr) [BitTags K] :=
  tagAt_typed (atBit i)

theorem lt_of_atBit {i : Nat} {A : Ty Empty} (h : At (List.ofFn (fun _ : Fin (K + 1) => Bit)) i A) : i < K + 1 := by
  have := (List.getElem?_eq_some_iff.mp h).1
  simpa using this

theorem eq_of_atBit {i : Nat} {A : Ty Empty} (h : At (List.ofFn (fun _ : Fin (K + 1) => Bit)) i A) : A = Bit :=
  Option.some.inj (h.symm.trans (atBit ⟨i, lt_of_atBit h⟩))

/-- One region for each block gives the rows of the table. -/
def freeOfBlocks {E : Ty Empty} (fr : Fin (K + 1) → Region signature.Instr)
    (h : ∀ i, ValueBranches [Bit] (fr i) [E]) : FreeRows (List.ofFn (fun _ : Fin (K + 1) => Bit)) E :=
  fun i _ hi => ⟨fr ⟨i, lt_of_atBit hi⟩, (eq_of_atBit hi).symm ▸ h ⟨i, lt_of_atBit hi⟩⟩

/-- A state of the router table at row `i`, from a Bit. -/
theorem rowState_typed (i : Fin (K + 1)) :
    ValueBranches [Bit] (.br 0 (injTm K i (.inl (.var 0))) : Region signature.Instr) [States K] :=
  .br rfl (injTm_typed (.inl (.var rfl)) K i)

/-- The start tag paired with the captured input: the routed entry of a
table whose entry jumps to block `s` with the input. -/
theorem entryTag_typed (s : Fin (K + 1)) :
    ValueBranches [Bit] (.br 0 (.inr (.pair (.var 0) (packedExitArg s.val (.var 0)))) : Region signature.Instr)
      [Silmaril.coprod Bit (Silmaril.product Bit (BitTags K))] := by
  cases bitTag_typed (K := K) s with
  | br ho hv =>
    cases Option.some.inj ho
    exact .br rfl (.inr (.pair (.var rfl) hv))

/-- The checked facts that relate a table of `K + 1` blocks, entered at
block `s`, to the router table `t` with `K + 1` rows. -/
structure TagCert {e : Region signature.Instr} {blocks : Fin (K + 1) → Region signature.Instr}
    (he : ValueBranches [Bit] e (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit]))
    (hb : ∀ i, ValueBranches [Bit, Bit] (blocks i) (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit]))
    (t : Router K) (s : Fin (K + 1)) where
  /-- The capture-free row of each block, with its exits tagged. -/
  free : Fin (K + 1) → Region signature.Instr
  free_typed : ∀ i, ValueBranches [Bit] (free i) [Silmaril.coprod Bit (BitTags K)]
  /-- From a tag to a state of the router table. -/
  toStates : ofType (Φ := signature.Instr) (BitTags K) ⟶ ofType (States K)
  /-- The routed entry is the start tag with the captured input. -/
  entry : ofRegion (entry_route (fun _ : Fin (K + 1) => Bit) he) = ofRegion (entryTag_typed s)
  /-- Each row of the readback is the capture-free row whiskered by the
  captured input and followed by `dropCase`. -/
  rows : ∀ j, ofRegion (orderedRow (fun _ : Fin (K + 1) => Bit) hb j).property =
    ofRegion (seqValueBranches
      (whiskerLeftRegion_typed Bit ((freeOfBlocks free free_typed) (atGet _ j)).property)
      (dropCase_typed (X := Bit) (B := Bit) (A := BitTags K)))
  /-- The tag of block `i` is sent to row `i`. -/
  tags : ∀ i, ofRegion (bitTag_typed i) ≫ toStates = ofRegion (rowState_typed i)
  /-- The capture-free row of block `i`, with its tags sent to states, is
  row `i` of the router table. -/
  step : ∀ i, ofRegion (free_typed i) ≫
      ((sumIso (Φ := signature.Instr) Bit (BitTags K)).hom ≫ coprod.map (𝟙 _) toStates) =
    (ofRegion bitState_typed ≫ ofRegion (t.rows_typed i)) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
