module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Grammar.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TagsGrammar

/-! # The request and reply grammar at every size: rows, entry and tag map

No seed and no quotient law is added. Default Paper is unchanged. The
two-block reader of #5340 is unchanged.

## Bottom-up, for a variable index

* `packedExitArg_rename_var0`, `packedExitArg_subst_var0`: a tag built on
  the newest variable is unchanged by a renaming or a substitution that
  fixes that variable. Induction on the index.
* `carryExit_exit`, `carryExit_block`: the routed exit at the exit label
  and at the label of a block, for any size.

## Every generated row, for every table and every size (default Paper)

* `NTable.row_lifted`: the readback row of block `i` of the table `d` is
  its capture-free row whiskered by the captured input and followed by
  `dropCase`. Both leaves are handled for a variable index by the lemmas
  above and product β.
* `NTable.row_cert`: the same at the parameter type that the readback
  gives the row, `(List.ofFn R).get j`. That type is `Bit` by a proved
  equality, and the equation is transported along it.
* `NTable.entry_tag`: the routed entry is the start tag with the
  captured input.
* `NTable.readback_tags`: so the packed readback of **every table of the
  grammar, at every size**, is the capture-free loop on its tags entered
  at the start tag. This is #5344's capture erasure with its hypotheses
  discharged for the grammar.

## The map from tags to states, for every size

* `tagsFold_tag`: `tagsFold` folds one region for each block into an arrow
  out of the tags by recursion on the list; at the tag of a block it is
  the region of that block.
* `toStatesN_tag`: `toStatesN K` sends the tag of block `i` to row `i`.
  These are the injection equations of the `tags` field of `TagCert`.

## The certificate, and the one field that remains

Three of the four fields of `TagCert` are now proved for every table and
size. The fourth is the step equation of each row:

`Task.nStep d`: for every block `i`, the capture-free row `d.free i`
followed by `toStatesN K` on its repeat side is row `i` of `d.router`
entered from a Bit.

It is not proved for a variable size. It is an equation between the
arrows of two explicit regions for each row. Its fixed-size proofs
compute with a concrete region from tags to states; for a variable size
that region and `injTm K j` do not compute under renaming and
substitution, so it needs lemmas for those. I did not prove them.

* `NTable.cert_of_step`: the step equations give the certificate.
* `NTable.bitPointed_of_step`, `NTable.complete_of_step`: the #5332
  certificate, and the supported-model iff for two tables of any two
  sizes. Every row is labelled, so the router tables are `Tidy`; the iff
  is in the opt-in quotient and for the supported models.

## Size three

* `cycleN_source`: the cycle of #5344 is the table `cycleN l` of the
  grammar.
* `cycleN_step`: its step equations, from #5344's fixed-size proof and
  `tags_ext`.
* `cycleN_hasCert`: so the cycle has its certificate through the uniform
  construction: rows, entry and tag map are the instances at size three
  of the theorems above.

## Not covered

* `Task.nStep` for a variable size, and so the certificate and the iff
  for every table of the grammar without a hypothesis.
* Typing of `NTable.flat` in the flat judgment, and a reader for more
  than two blocks.
* Blocks that use the captured input, and completeness in default Paper.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofRegion ofType)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking
  (Valid.symm Valid.trans)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity
open Silmaril.DeBruijn (lift)
open CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (whiskerLeftRegion whiskerLeftRegion_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (iterate sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep orderedRow entry_route carryExit)

variable {K K' : Nat}

/-! ## Bottom-up, for a variable index -/

theorem packedExitArg_rename_var0 (j : Nat) (ρ : Nat → Nat) (h : ρ 0 = 0) :
    (packedExitArg j (.var 0) : Tm signature.Instr).rename ρ = packedExitArg j (.var 0) :=
  Tables.packedExitArg_rename0 j ρ h

theorem packedExitArg_subst_var0 (j : Nat) (θ : Nat → Tm signature.Instr) (h : θ 0 = .var 0) :
    (packedExitArg j (.var 0) : Tm signature.Instr).subst θ = packedExitArg j (.var 0) :=
  Tables.packedExitArg_subst0 j θ h

theorem carryExit_exit : (carryExit 1 (K + 1) (K + 1) : Region signature.Instr) = .br 0 (.inl (.var 0)) :=
  Tables.carry_exit

theorem carryExit_block (c : Nat) (j : Fin (K + 1)) :
    (carryExit c (K + 1) j.val : Region signature.Instr) =
      .br 0 (.inr (.pair (.var (c + 1)) (packedExitArg j.val (.var 0)))) :=
  Tables.carry_block c j

/-! ## The map from tags to states -/

/-- At the tag of a block, the fold is the region of that block. -/
theorem tagsFold_tag {E : Ty Empty} (L : LCtx (Ty Empty)) (β : FreeRows L E) {i : Nat} {A : Ty Empty}
    (h : At L i A) : ofRegion (tagAt_typed h) ≫ tagsFold L β = ofRegion (β h).property :=
  Tables.tag_fold L β h

/-- The map from tags to states sends the tag of block `i` to row `i`. -/
theorem toStatesN_tag (i : Fin (K + 1)) :
    ofRegion (bitTag_typed i) ≫ toStatesN K = ofRegion (rowState_typed i) :=
  Tables.toStatesN_tag i

namespace NTable

variable (d : NTable K) (d' : NTable K')

/-! ## Every generated row -/

/-- The readback row of a block is its capture-free row whiskered by the
captured input and followed by `dropCase`. Default Paper, every size. -/
theorem row_lifted (i : Fin (K + 1)) :
    Paper.Eqv [Silmaril.product Bit Bit] (seqRegion (whiskerLeftRegion (d.free i)) dropCase)
      (Paper.RetainedLet.unpackBody ((d.blocks i).lsubst (carryExit 1 (K + 1))))
      [Silmaril.coprod Bit (Silmaril.product Bit (BitTags K))] :=
  Tables.nrow_lift d i

/-- The same at the parameter type that the readback gives the row. -/
theorem row_cert (j : Fin (List.ofFn (fun _ : Fin (K + 1) => Bit)).length) :
    ofRegion (orderedRow (fun _ : Fin (K + 1) => Bit) d.blocks_typed j).property =
      ofRegion (seqValueBranches
        (whiskerLeftRegion_typed Bit ((freeOfBlocks d.free d.free_typed) (atGet _ j)).property)
        (dropCase_typed (X := Bit) (B := Bit) (A := BitTags K))) :=
  Tables.nrow_cert d j

/-- The routed entry is the start tag with the captured input. -/
theorem entry_tag :
    ofRegion (entry_route (fun _ : Fin (K + 1) => Bit) d.entry_typed) = ofRegion (entryTag_typed d.start) :=
  Tables.nentry d

/-- The packed readback of every table of the grammar is the capture-free
loop on its tags, entered at the start tag. Default Paper, every size. -/
theorem readback_tags :
    ofRegion (packedReadbackRep (fun _ : Fin (K + 1) => Bit) d.entry_typed d.blocks_typed).property =
      ofRegion (bitTag_typed d.start) ≫ iterate (freeDisp _ (freeOfBlocks d.free d.free_typed)) :=
  Tables.nreadback_tags d

/-! ## The certificate from the step equations -/

/-- The step equations of the rows give the certificate of the table. -/
theorem cert_of_step (h : Task.nStep d) :
    Nonempty (TagCert d.entry_typed d.blocks_typed d.router d.start) :=
  ⟨Tables.ncert d h⟩

/-- And the certificate at the two constant inputs. -/
theorem bitPointed_of_step (h : Task.nStep d) :
    BitPointed d.source (fun i => some (d.label i)) d.act (fun _ => d.start) :=
  Tables.nbitPointed d h

/-- Two tables of any two sizes whose rows satisfy the step equations are
equal at the source entry exactly when they are valid in every supported
model. -/
theorem complete_of_step (h : Task.nStep d) (h' : Task.nStep d') :
    Eqv false [Bit] d.source d'.source [Bit] ↔ Valid d.source_typed.hasType d'.source_typed.hasType :=
  Tables.ncomplete d d' h h'

end NTable

/-! ## Size three -/

/-- The cycle of #5344 is a table of the grammar. -/
theorem cycleN_source (l : Bool) : (cycleN l).source = cycleSource l :=
  Tables.cycleN_source l

/-- The step equations of the cycle. -/
theorem cycleN_step (l : Bool) : Task.nStep (cycleN l) :=
  Tables.cycleN_step l

/-- The cycle has its certificate through the uniform construction. -/
theorem cycleN_hasCert (l : Bool) :
    Nonempty (TagCert (cycleN l).entry_typed (cycleN l).blocks_typed (cycleN l).router (cycleN l).start) :=
  (cycleN l).cert_of_step (cycleN_step l)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
