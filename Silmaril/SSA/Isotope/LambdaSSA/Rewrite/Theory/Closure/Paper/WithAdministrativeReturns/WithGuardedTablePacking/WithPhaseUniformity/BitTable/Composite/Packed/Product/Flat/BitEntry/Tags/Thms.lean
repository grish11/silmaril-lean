module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.Tags.Cycle.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Packed.Product.Flat.BitEntry.PollTable.Read.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Projection.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Cycle3

/-! # Tables with any number of blocks

No seed and no quotient law is added. Default Paper is unchanged.

## Reusable, for any number of blocks (default Paper)

* `freeDisp_tag`, `tags_ext`: the tags of any list of blocks. At the tag
  of a block the step on the tags is the row of that block, and two
  arrows out of the tags are equal when they agree at every tag.
* `dispatcherRep_iterate`: **capture erasure for a dispatcher of any
  size.** A captured dispatcher whose rows are capture-free rows
  whiskered by the captured input and followed by `dropCase` iterates as
  the step on the tags, after the captured input is dropped. It is
  proved by induction on the list of blocks, for any capture type, block
  parameter types and exit type. It generalizes #5314's lemma for two
  rows.
* `packedReadback_erase`: so the packed readback of a table with any
  number of such rows, entered at a tag, is the capture-free loop on the
  tags entered at that tag.

## Reusable, for `K + 1` Bit blocks and a router table with `K + 1` rows

A `TagCert` collects four checked facts about a table and a router
table: the routed entry, the lifted form of each readback row, a map
from tags to states that sends tag `i` to row `i`, and one step equation
for each row. Given a certificate:

* `TagCert.readback`: the packed readback is the router table entered at
  the start row. Default Paper: capture erasure, then the roll law of
  iteration along the map from states to tags, of which the map of the
  certificate is a section.
* `TagCert.source_eqv_entered`: the table is the router table entered at
  the start row, in the table-packing quotient. The packing seed is the
  only opt-in rule.
* `TagCert.bitPointed`: the certificate of #5332.
* `TagCert.eqv_iff_entered`: two tables with certificates, of any two
  sizes, are equal exactly when their router tables are equal at the
  start rows.
* `TagCert.complete`: under the explicit hypotheses that both router
  tables are `Tidy`, two tables with certificates are equal at the source
  entry exactly when they are valid in every supported model.

## A cycle of three blocks

`cycleFlat l` is a scoped flat graph with three blocks in a cycle.

* `cycleFlat_typed`: it is typed in the flat judgment.
* `cycleSource_hasCert`: it has a certificate for `cycleRouter l`.
* `cycleSource_eqv_entered`, `cycleSource_bitPointed`,
  `cycleSource_complete`: the instances of the theorems above.
* `cycleSource_pollTable_complete`: a cycle of three blocks and any table
  of the two-block fragment are equal exactly when valid in every
  supported model.
* `cycleSource_eqv_selfTable`: the cycle of three blocks has the source
  of the two-block table whose blocks repeat themselves.
* `cycleSource_ne_neverTable`, `cycleSource_eqv_iff`: it is not a table
  that never leaves, and two cycles are equal exactly when their labels
  agree.

## Not covered: a certificate for every table of a grammar, for all sizes

The certificate of the cycle is proved for that table. Its four fields
are checked by computation at the size three. A proof that produces the
certificate for every table of the request and reply grammar and every
`K` is not given. It needs, for a variable block index and size:

* the readback row `unpackBody ((blocks i).lsubst (carryExit 1 n))` in
  its lifted form: the conditional in `carryExit` and `packedExitArg`
  under renaming and substitution do not compute for a variable index;
* the parameter type `(List.ofFn R).get j` of a readback row, which is
  `Bit` only up to a proved equality when `j` is a variable;
* a region from tags to states for every `K`, and `injTm K j` under
  substitution.

The reader of #5340 is not extended. Tables that are not tidy, blocks
that use the captured input, and completeness in default Paper are not
covered.
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
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (whiskerLeftRegion_typed)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (iterate sumIso)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.Projection (productSnd)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep dispatcherRep orderedRow entry_route)

/-! ## Any number of blocks -/

section AnyList

variable {X D P : Ty Empty}

/-- At the tag of a block, the step on the tags is the row of that block. -/
theorem freeDisp_tag (L : LCtx (Ty Empty)) (β : FreeRows L (Silmaril.coprod D P)) {i : Nat} {A : Ty Empty}
    (h : At L i A) :
    ofRegion (tagAt_typed h) ≫ freeDisp L β =
      ofRegion (β h).property ≫ (sumIso (Φ := signature.Instr) D P).hom :=
  Tables.tag_free L β h

/-- Two arrows out of the tags are equal when they agree at every tag. -/
theorem tags_ext (L : LCtx (Ty Empty)) {W : Paper.TypeCategory (τ := Ty Empty) signature.Instr}
    {f g : ofType (Φ := signature.Instr) (packedExitType L) ⟶ W}
    (h : ∀ ⦃i : Nat⦄ ⦃A : Ty Empty⦄ (hi : At L i A),
      ofRegion (tagAt_typed hi) ≫ f = ofRegion (tagAt_typed hi) ≫ g) : f = g :=
  Tables.tags_ext L h

/-- A captured dispatcher of any number of rows, each a capture-free row
whiskered by the captured input and followed by `dropCase`, iterates as
the step on the tags after the captured input is dropped. -/
theorem dispatcherRep_iterate (L : LCtx (Ty Empty))
    (rows : ∀ i : Fin L.length, {r : Region signature.Instr // ValueBranches [Silmaril.product X (L.get i)] r
      [Silmaril.coprod D (Silmaril.product X (packedExitType L))]})
    (β : FreeRows L (Silmaril.coprod D (packedExitType L)))
    (e : ∀ i : Fin L.length, ofRegion (rows i).property =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed X (β (atGet L i)).property)
        (dropCase_typed (X := X) (B := D) (A := packedExitType L)))) :
    iterate (ofRegion (dispatcherRep X L rows).property ≫
        (sumIso (Φ := signature.Instr) D (Silmaril.product X (packedExitType L))).hom) =
      productSnd (ofType (Φ := signature.Instr) X) (ofType (packedExitType L)) ≫ iterate (freeDisp L β) :=
  Tables.disp_drop L rows β e

/-- The packed readback of a table with any number of such rows, entered
at a tag, is the capture-free loop on the tags entered at that tag. -/
theorem packedReadback_erase {n : Nat} (R : Fin n → Ty Empty) {e : Region signature.Instr}
    {blocks : Fin n → Region signature.Instr} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D]))
    (β : FreeRows (List.ofFn R) (Silmaril.coprod D (packedExitType (List.ofFn R))))
    (hrows : ∀ j, ofRegion (orderedRow R hb j).property =
      ofRegion (seqValueBranches (whiskerLeftRegion_typed X (β (atGet _ j)).property)
        (dropCase_typed (X := X) (B := D) (A := packedExitType (List.ofFn R)))))
    {t : Tm signature.Instr} (ht : Tm.BranchValue [X] t (packedExitType (List.ofFn R)))
    (hentry : ofRegion (entry_route R he) =
      ofRegion (r := .br 0 (.inr (.pair (.var 0) t)))
        (.br (L := [Silmaril.coprod D (Silmaril.product X (packedExitType (List.ofFn R)))]) rfl
          (.inr (.pair (.var rfl) ht)))) :
    ofRegion (packedReadbackRep R he hb).property =
      ofRegion (r := .br 0 t) (.br rfl ht) ≫ iterate (freeDisp (List.ofFn R) β) :=
  Tables.readback_erase R he hb β hrows ht hentry

end AnyList

/-! ## Certificates -/

namespace TagCert

variable {K K' : Nat} {e e' : Region signature.Instr} {blocks : Fin (K + 1) → Region signature.Instr}
  {blocks' : Fin (K' + 1) → Region signature.Instr}
  {he : ValueBranches [Bit] e (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit])}
  {hb : ∀ i, ValueBranches [Bit, Bit] (blocks i) (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit])}
  {he' : ValueBranches [Bit] e' (List.ofFn (fun _ : Fin (K' + 1) => Bit) ++ [Bit])}
  {hb' : ∀ i, ValueBranches [Bit, Bit] (blocks' i) (List.ofFn (fun _ : Fin (K' + 1) => Bit) ++ [Bit])}
  {t : Router K} {t' : Router K'} {s : Fin (K + 1)} {s' : Fin (K' + 1)}

/-- The table of a certificate is a guarded source. -/
theorem typed (he : ValueBranches [Bit] e (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit]))
    (hb : ∀ i, ValueBranches [Bit, Bit] (blocks i) (List.ofFn (fun _ : Fin (K + 1) => Bit) ++ [Bit])) :
    ValueBranches [Bit] (.cfg e (K + 1) blocks) [Bit] :=
  .cfg (fun _ : Fin (K + 1) => Bit) he hb

/-- The packed readback is the router table entered at the start row, on
the input as its Bit. Default Paper. -/
theorem readback (c : TagCert he hb t s) :
    ofRegion (packedReadbackRep (fun _ : Fin (K + 1) => Bit) he hb).property =
      ofRegion bitState_typed ≫ ofRegion (t.entered_typed s) :=
  Tables.cert_readback c

/-- The table is the router table entered at the start row, in the
table-packing quotient. -/
theorem source_eqv_entered (c : TagCert he hb t s) :
    WithGuardedTablePacking.Eqv false [Bit] (.cfg e (K + 1) blocks)
      (seqRegion (.br 0 (.inl (.var 0))) (t.entered s)) [Bit] :=
  Tables.cert_source c

/-- The certificate at the two constant inputs. -/
theorem bitPointed {label : Fin (K + 1) → Option Bool} {act : Fin (K + 1) → Bool → Bool → Act K}
    (c : TagCert he hb (Router.ofSpin label act) s) :
    BitPointed (.cfg e (K + 1) blocks) label act (fun _ => s) :=
  Tables.cert_bitPointed c

/-- Two tables with certificates are equal at the source entry exactly
when their router tables are equal at the start rows. -/
theorem eqv_iff_entered (c : TagCert he hb t s) (c' : TagCert he' hb' t' s') :
    Eqv false [Bit] (.cfg e (K + 1) blocks) (.cfg e' (K' + 1) blocks') [Bit] ↔
      Eqv false [State] (t.entered s) (t'.entered s') [Bit] :=
  Tables.cert_eqv_iff_entered c c'

/-- Two tables with certificates in tidy router tables are equal at the
source entry exactly when they are valid in every supported model. -/
theorem complete {label : Fin (K + 1) → Option Bool} {act : Fin (K + 1) → Bool → Bool → Act K}
    {label' : Fin (K' + 1) → Option Bool} {act' : Fin (K' + 1) → Bool → Bool → Act K'}
    (ht : Tidy label act) (ht' : Tidy label' act')
    (c : TagCert he hb (Router.ofSpin label act) s) (c' : TagCert he' hb' (Router.ofSpin label' act') s') :
    Eqv false [Bit] (.cfg e (K + 1) blocks) (.cfg e' (K' + 1) blocks') [Bit] ↔
      Valid (typed he hb).hasType (typed he' hb').hasType :=
  Tables.cert_complete ht ht' c c'

end TagCert

/-! ## A cycle of three blocks -/

/-- The flat graph of the cycle is typed in the flat judgment. -/
theorem cycleFlat_typed (l : Bool) :
    LambdaSSA.FiniteCFG.HasType (.snoc .nil Bit) (fun _ : Fin 3 => Bit) (fun _ : Fin 1 => Bit) (cycleFlat l) :=
  Tables.cyc3_flat_typed l

/-- The cycle has a certificate for its router table, entered at block `0`. -/
theorem cycleSource_hasCert (l : Bool) :
    Nonempty (TagCert cycleEntry_typed (cycleBlocks_typed l) (cycleRouter l) 0) :=
  ⟨Tables.cycleCert l⟩

/-- The cycle is its router table entered at row `0`, in the
table-packing quotient. -/
theorem cycleSource_eqv_entered (l : Bool) :
    WithGuardedTablePacking.Eqv false [Bit] (cycleSource l)
      (seqRegion (.br 0 (.inl (.var 0))) ((cycleRouter l).entered 0)) [Bit] :=
  Tables.cyc3_source_entered l

theorem cycleSource_bitPointed (l : Bool) :
    BitPointed (cycleSource l) (fun _ => some l) cycleAct (fun _ => (0 : Fin 3)) :=
  Tables.cyc3_bitPointed l

/-- Two cycles are equal at the source entry exactly when they are valid
in every supported model. -/
theorem cycleSource_complete (l l' : Bool) :
    Eqv false [Bit] (cycleSource l) (cycleSource l') [Bit] ↔
      Valid (cycleSource_typed l).hasType (cycleSource_typed l').hasType :=
  Tables.cyc3_complete l l'

/-- A cycle of three blocks and a table of the two-block fragment are
equal at the source entry exactly when they are valid in every supported
model. -/
theorem cycleSource_pollTable_complete (l : Bool) (d : PollTable) :
    Eqv false [Bit] (cycleSource l) d.source [Bit] ↔
      Valid (cycleSource_typed l).hasType d.source_typed.hasType :=
  Tables.cyc3_poll_complete l d

/-- The cycle of three blocks has the source of the two-block table whose
blocks repeat themselves. -/
theorem cycleSource_eqv_selfTable (l : Bool) : Eqv false [Bit] (cycleSource l) (selfTable l).source [Bit] :=
  Tables.cyc3_self l

/-- The cycle is not a table that never leaves. -/
theorem cycleSource_ne_neverTable (l l' : Bool) :
    ¬ Eqv false [Bit] (cycleSource l) (neverTable l').source [Bit] :=
  Tables.cyc3_never l l'

/-- Two cycles are equal exactly when their labels agree. -/
theorem cycleSource_eqv_iff (l l' : Bool) :
    Eqv false [Bit] (cycleSource l) (cycleSource l') [Bit] ↔ l = l' :=
  Tables.cyc3_label l l'

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
