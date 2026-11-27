module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceReadback.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Fragment.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.SourceReadback

/-! # The readback of the checked table and the packed program

The checked table that is reified from an elaborated flat graph and the
typed packed program of the same graph are compared, and the comparison
is composed with the square from the φ source.

## The common observable

Both sides are observed as weak trees over the events of one model, at
the same decoded captures, returning one value: the payload of the exit
that was taken, injected at the position of that exit in the packed sum
of the ordered exits.

* The readback of the table is a LetCase term whose result type is that
  packed sum. Its tree returns the packed value.
* The packed program is a region with one label. Its tree returns the
  packed value at label `0`.

So the two trees are not equal as written. They are equal after the exit
adapter `fun value => (0, value)` on the readback side. On the input
side the readback runs in the environment of the decoded captures, and
the packed program runs on the encoded input record above any ambient
environment; these describe the same captures.

## The model

The comparison is in a model of the ordered weak-tree semantics: a typed
interpretation of the primitives, an erased one, and their
compatibility. The readback of the table and the term of the flat graph
are natively equal, not syntactically equal, so the comparison uses that
native equality is sound for the tree of an erased term. That holds here
because the equations treat only instructions of bottom effect as pure,
and the typed interpretation gives those as functions; it is proved by
the existing soundness of the Kleisli denotation and the existing
agreement of the typed denotation with the erased tree. The environment
has to encode a typed one, which the decoded captures do.

## What is not here

The ranked institution of the atom regressions gives the table an arrow
in a category, for a model of regions over a signature in `Type`, with
the packed sum unpacked into the ordered exits. This file gives the table
a weak tree, for a tree model over sorts in a higher universe, with the
exits packed. The arrow and the tree are not related here. That edge
needs the weak-tree Kleisli category as a model of regions at the same
signature and universe, and the existing equation between the arrow of
the table and the denotation of its readback, read in that model.
-/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceReadback

open Silmaril.Isotope.LambdaSSA.Acyclic
open Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase (Witness)
open LambdaSSA (Region FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue BoundEnv)
open LetCase.LocallyNameless (Derivation Equiv)
open Morphism.CaseSSA (erase)
open NamedFlat.Entry.Record (Input)

universe u v

variable {κ : Type (u + 1)} [AtomValues κ] [DecidableEq κ] {Φ : Type v} [HasTy Φ (Ty κ)]
  [HasEff Φ Bool] {Events : Type u → Type u}

local notation "Atoms" => AtomValues.carrier (κ := κ)
local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty κ))

/-- Native equality is sound for the weak tree of an erased term, in a model
whose typed and erased primitives are compatible, at an environment that
encodes a typed one. -/
theorem term_eq_of_equiv (M : Model (κ := κ) Events Φ) {n : Nat} {β : BoundCtx (Ty κ) n}
    {a b : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty κ} (h : Equiv false Γ₀ β a b A)
    (da : Derivation Φ Γ₀ β a A) (db : Derivation Φ Γ₀ β b A)
    (ρ : BoundEnv (Ty.denote Atoms) β) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val = encodeValue Atoms (β.get i) (ρ i)) :
    LambdaSSA.Semantics.Interaction.term M.raw env (erase a) =
      LambdaSSA.Semantics.Interaction.term M.raw env (erase b) :=
  term_eq_of_equiv_proof M h da db ρ env agree

section Packed

variable {blocks exits n : Nat} {β : BoundCtx (Ty κ) n} {R : Fin blocks → Ty κ}
  {D : Fin exits → Ty κ} {g : FiniteCFG Φ blocks exits n}

omit [DecidableEq κ] in
/-- The typed packed program of a flat graph, on the packed input record,
runs as the graph does on the decoded captures, with the exit packed at
its single label. -/
theorem packed_program (M : Model (κ := κ) Events Φ) (typed : g.HasType β R D)
    (record : Input β) (ambient : Env (Sigma Atoms)) :
    region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry typed).code =
      (region M.raw (NamedFlat.Entry.inputEnv β record) g.erase >>= fun p =>
        pure (FiniteCFG.packedTreeOutput p)) :=
  packed_program_proof M typed record ambient

end Packed

section Table

variable {size exits n : Nat} {β : BoundCtx (Ty κ) n} {R : Fin (size + 1) → Ty κ}
  {D : Fin exits → Ty κ} {g : FiniteCFG Φ (size + 1) exits n}

/-- The readback of the checked table of a flat graph in the fragment has
the weak tree of the flat graph, with the exit packed into the value. -/
theorem checkedTable_tree (M : Model (κ := κ) Events Φ) (w : Witness g β R D)
    (h : w.Delimited) (ranked : Positional.Rank.check (FlatLetCase.localTargets g) = true)
    (ρ : BoundEnv (Ty.denote Atoms) β) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val = encodeValue Atoms (β.get i) (ρ i)) :
    LambdaSSA.Semantics.Interaction.term M.raw env
        (erase (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)).toLetCase.1) =
      (region M.raw env g.erase >>= fun out => pure (Region.packedExitValue out.1 out.2)) :=
  checkedTable_tree_proof M w h ranked ρ env agree

/-- The readback of the checked table and the typed packed program of the
same flat graph have the same weak tree, up to the exit adapter: the
readback returns the packed exit value, and the packed program returns
it at its single label. -/
theorem readback_packed (M : Model (κ := κ) Events Φ) (w : Witness g β R D)
    (h : w.Delimited) (ranked : Positional.Rank.check (FlatLetCase.localTargets g) = true)
    (typed : g.HasType β R D) (record : Input β) (ambient : Env (Sigma Atoms)) :
    (LambdaSSA.Semantics.Interaction.term M.raw (NamedFlat.Entry.inputEnv β record)
        (erase (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)).toLetCase.1) >>=
        fun value => pure (0, value)) =
      region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry typed).code :=
  readback_packed_proof M w h ranked typed record ambient

end Table

section Recount

variable {a b exits n : Nat}

omit [AtomValues κ] [DecidableEq κ] [HasTy Φ (Ty κ)] [HasEff Φ Bool] in
/-- Recounting keeps the erased region. -/
theorem recount_erase (count : a = b) (g : FiniteCFG Φ a exits n) :
    (recount count g).erase = g.erase :=
  recount_erase_proof count g

omit [AtomValues κ] [DecidableEq κ] [HasEff Φ Bool] in
/-- Recounting keeps the typing, with the packet types at the recounted
positions. -/
theorem recount_typed (count : a = b) {g : FiniteCFG Φ a exits n} {β : BoundCtx (Ty κ) n}
    {R : Fin a → Ty κ} {D : Fin exits → Ty κ} (typed : g.HasType β R D) :
    (recount count g).HasType β (fun i => R (Fin.cast count.symm i)) D :=
  recount_typed_proof count typed

end Recount

section Source

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping

variable {V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {n : Nat} {β : BoundCtx (Ty κ) n}

/-- From the φ source to the readback of the checked table, for a closed
forwarding table. Under the checks of the source square, and when the
elaborated graph has the shape of the fragment and passes the rank check,
there is a witness of the elaborated graph in the fragment, and the φ run
of the original graph at the ordered exits is the weak tree of the
readback of its checked table, up to the exit adapter. -/
theorem source_readback (graph : Phi.Graph V K P.Instr) (table : Phi.Forward.Table V K)
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
            pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) =
          (LambdaSSA.Semantics.Interaction.term M.raw (NamedFlat.Entry.inputEnv β record)
            (erase (w.checkedTable h
              (FlatLetCase.Witness.table_check w h ranked)).toLetCase.1) >>=
            fun value => pure (0, value)) :=
  source_readback_proof graph table exits inputs types exitType C valid isClosed fragment covered
    certificate declared count shaped

/-- The same with the inferred forwarding table. The hypotheses on the φ
graph are checks on the original graph; the shape and the rank check are
on the elaborated graph. -/
theorem source_readback_infer (graph : Phi.Graph V K P.Instr) (exits : List (Option K))
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
            pure (FiniteCFG.packedTreeOutput (treeExitNumber exits p))) =
          (LambdaSSA.Semantics.Interaction.term M.raw (NamedFlat.Entry.inputEnv β record)
            (erase (w.checkedTable h
              (FlatLetCase.Witness.table_check w h ranked)).toLetCase.1) >>=
            fun value => pure (0, value)) :=
  source_readback_infer_proof graph exits inputs arrivals rank types exitType C inScope claims
    acyclic fragment covered certificate declared count shaped

end Source

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceReadback
