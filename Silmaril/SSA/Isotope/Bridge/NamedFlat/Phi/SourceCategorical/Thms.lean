module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceCategorical.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceReadback.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.SourceCategorical

/-! # From the φ source to the arrow of the checked table

The checked table that is reified from an elaborated flat graph has an
arrow in the weak-tree Kleisli model: the native denotation of its
region, from the captured context to the ordered exits. This file
relates that arrow to the readback of the table, to the packed program
of the graph, and to the φ run of the original graph.

## The common observable

All sides are weak trees over the events of one model of the ordered
weak-tree semantics, at the same supplied record.

* The arrow is observed at the record as a point of the product of the
  captured context. Its tree returns the position of the exit taken and
  the encoded payload.
* The φ run returns the exit taken and its payload; the exit is numbered
  by its position in the ordered exits.
* The flat graph returns the position and the payload.
* The packed program returns the payload packed at label `0`.

At the ordered exits the arrow, the flat graph and the φ run have the
same tree, with no adapter. The packed program has the tree of the arrow
with each exit packed at label `0`.

## How the edge is closed

The law `Table.toLetCase_denote` equates the arrow with the categorical
denotation of the readback, followed by the unpacking of the packed sum
into the ordered exits. In the weak-tree model that denotation returns
the tree of the erased readback, and unpacking then packing an exit is
the identity on encoded values. The comparison of the readback with the
packed program and the square from the φ source then give the
statements here. Packing is injective on exits, which removes it from
the comparison at the ordered exits.

## What is not claimed

The arrow is in the weak-tree Kleisli model only. The ranked institution
of the atom regressions has its models over a signature in `Type`, in
categories with objects in `Type 1` and morphisms in `Type`; the
weak-tree model has sorts in `Type (u + 1)` and a category one universe
higher, so it is not one of those models, and no statement here is
about them. The arrow is the region denotation that the institution's
denotation of the entry of a checked table unfolds to.
-/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceCategorical

open Silmaril.Isotope.LambdaSSA.Acyclic
open Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase (Witness)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.WeakTree
open LambdaSSA (Region FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues typeModel)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open LetIter.Semantics.Categorical (boundLookup)
open NamedFlat.Entry.Record (Input)
open NamedFlat.Phi.SourceReadback (recount)

universe u v

variable {κ : Type (u + 1)} [AtomValues κ] [DecidableEq κ] {Φ : Type v} [HasTy Φ (Ty κ)]
  [HasEff Φ Bool] {Events : Type u → Type u}

attribute [local instance] typeModel

local notation "Atoms" => AtomValues.carrier (κ := κ)
local notation "T" => LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)

omit [DecidableEq κ] in
/-- The context map of the packed record has the fields of the record. -/
theorem packed_field {n : Nat} (β : BoundCtx (Ty κ) n) (record : Input β) (i : Fin n) :
    boundLookup T i (contextMap T β (packed β record)).2 =
      NamedFlat.Entry.Record.field β record i :=
  packed_field_proof β record i

section Table

variable {size exits n : Nat} {β : BoundCtx (Ty κ) n} {R : Fin (size + 1) → Ty κ}
  {D : Fin exits → Ty κ} {g : FiniteCFG Φ (size + 1) exits n}

/-- The arrow of the checked table of a flat graph in the fragment, at
the supplied record, has the weak tree of the flat graph at the ordered
exits. -/
theorem table_arrow (M : Model (κ := κ) Events Φ) (w : Witness g β R D)
    (h : w.Delimited) (ranked : Positional.Rank.check (FlatLetCase.localTargets g) = true)
    (record : Input β) :
    exitTree (List.ofFn D)
        (arrow M (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)))
        (packed β record) =
      region M.raw (NamedFlat.Entry.inputEnv β record) g.erase :=
  table_arrow_proof M w h ranked record

/-- The arrow of the checked table, with each exit packed at label `0`,
has the weak tree of the typed packed program of the same flat graph.
This composes the law of the table with `readback_packed`. -/
theorem readback_arrow (M : Model (κ := κ) Events Φ) (w : Witness g β R D)
    (h : w.Delimited) (ranked : Positional.Rank.check (FlatLetCase.localTargets g) = true)
    (typed : g.HasType β R D) (record : Input β) (ambient : Env (Sigma Atoms)) :
    (exitTree (List.ofFn D)
        (arrow M (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)))
        (packed β record) >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry typed).code :=
  readback_arrow_proof M w h ranked typed record ambient

end Table

section Source

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping

variable {V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {n : Nat} {β : BoundCtx (Ty κ) n}

/-- From the φ source to the arrow of the checked table, for a closed
forwarding table. Under the hypotheses of `source_readback`, the φ run
of the original graph, with its exit numbered in the ordered exits, is
the arrow of the checked table of the elaborated graph at the supplied
record, observed at the ordered exits. -/
theorem source_arrow (graph : Phi.Graph V K P.Instr) (table : Phi.Forward.Table V K)
    (exits : List (Option K)) (inputs : List V) (types : V → Ty κ)
    (exitType : Option K → Ty κ) (C : Captures (Phi.Forward.Name V K) β)
    (valid : Phi.Forward.check graph table = true)
    (isClosed : Phi.Forward.closed graph table exits inputs = true)
    (fragment : NamedFlat.Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, C.names i = some (Sum.inl z))
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, β.get i = lifted (forwardTypes types) (C.names i)) {size : Nat}
    (count : (Versioning.compile (Phi.OrderedExits.lower
      (Phi.Forward.forward graph table))).blocks.length = size + 1)
    (shaped : (NamedFlat.compile (Phi.OrderedExits.lower (Phi.Forward.forward graph table)) exits
        C.names).all (fun code => FlatLetCase.delimitedShape (recount count code) &&
          Positional.Rank.check (FlatLetCase.localTargets (recount count code))) = true) :
    ∃ (code : FiniteCFG P.Instr (Versioning.compile (Phi.OrderedExits.lower
          (Phi.Forward.forward graph table))).blocks.length exits.length n)
      (w : Witness (recount count code) β
        (fun i => internal (Phi.Forward.forward graph table) (forwardTypes types)
          (Fin.cast count.symm i)) (external exits exitType))
      (h : w.Delimited)
      (ranked : Positional.Rank.check (FlatLetCase.localTargets (recount count code)) = true),
      NamedFlat.compile (Phi.OrderedExits.lower (Phi.Forward.forward graph table)) exits C.names =
        some code ∧
      ∀ {Events : Type u → Type u} (M : Model (κ := κ) Events P.Instr) (record : Input β),
        (Phi.OrderedExits.run (treeModel M.raw) graph (C.store record ∘ Sum.inl) >>= fun p =>
            pure (treeExitNumber exits p)) =
          exitTree (List.ofFn (external exits exitType))
            (arrow M (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)))
            (packed β record) :=
  source_arrow_proof graph table exits inputs types exitType C valid isClosed fragment covered
    certificate declared count shaped

/-- The same with the inferred forwarding table. The hypotheses on the φ
graph are checks on the original graph; the shape and the rank check are
on the elaborated graph. -/
theorem source_arrow_infer (graph : Phi.Graph V K P.Instr) (exits : List (Option K))
    (inputs : List V) (arrivals : Phi.GlobalSSA.Certificate V K) (rank : K → Nat)
    (types : V → Ty κ) (exitType : Option K → Ty κ) (C : Captures (Phi.Forward.Name V K) β)
    (inScope : Phi.OrderedExits.check graph exits inputs arrivals = true)
    (claims : Phi.Forward.claimed graph arrivals = true)
    (acyclic : Phi.Forward.ranked graph rank = true)
    (fragment : NamedFlat.Phi.plain graph = true)
    (covered : ∀ z ∈ inputs, ∃ i, C.names i = some (Sum.inl z))
    (certificate : certified graph types exitType = true)
    (declared : ∀ i, β.get i = lifted (forwardTypes types) (C.names i)) {size : Nat}
    (count : (Versioning.compile (Phi.OrderedExits.lower
      (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs)))).blocks.length = size + 1)
    (shaped : (NamedFlat.compile (Phi.OrderedExits.lower
        (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs))) exits C.names).all
        (fun code => FlatLetCase.delimitedShape (recount count code) &&
          Positional.Rank.check (FlatLetCase.localTargets (recount count code))) = true) :
    ∃ (code : FiniteCFG P.Instr (Versioning.compile (Phi.OrderedExits.lower
          (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs)))).blocks.length
          exits.length n)
      (w : Witness (recount count code) β
        (fun i => internal (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs))
          (forwardTypes types) (Fin.cast count.symm i)) (external exits exitType))
      (h : w.Delimited)
      (ranked : Positional.Rank.check (FlatLetCase.localTargets (recount count code)) = true),
      NamedFlat.compile (Phi.OrderedExits.lower
          (Phi.Forward.forward graph (Phi.Forward.infer graph exits inputs))) exits C.names =
        some code ∧
      ∀ {Events : Type u → Type u} (M : Model (κ := κ) Events P.Instr) (record : Input β),
        (Phi.OrderedExits.run (treeModel M.raw) graph (C.store record ∘ Sum.inl) >>= fun p =>
            pure (treeExitNumber exits p)) =
          exitTree (List.ofFn (external exits exitType))
            (arrow M (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)))
            (packed β record) :=
  source_arrow_infer_proof graph exits inputs arrivals rank types exitType C inScope claims
    acyclic fragment covered certificate declared count shaped

end Source

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceCategorical
