module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceCategorical.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceReadback.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Categorical.WeakTree.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceCategorical

open CategoryTheory
open Silmaril.Isotope.LambdaSSA.Acyclic
open Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase (Witness)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.WeakTree
open LambdaSSA (Region FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Categorical (ctxObj)
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

/-! ## The packed record -/

omit [DecidableEq κ] in
theorem packed_field_proof : {n : Nat} → (β : BoundCtx (Ty κ) n) → (record : Input β) →
    (i : Fin n) →
    boundLookup T i (contextMap T β (packed β record)).2 =
      NamedFlat.Entry.Record.field β record i
  | _, .nil, _, i => i.elim0
  | _, .snoc β A, record, i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact packed_field_proof β record.1 j

/-! ## The checked table of a flat graph -/

section Table

variable {size exits n : Nat} {β : BoundCtx (Ty κ) n} {R : Fin (size + 1) → Ty κ}
  {D : Fin exits → Ty κ} {g : FiniteCFG Φ (size + 1) exits n}

omit [DecidableEq κ] in
private theorem agree (record : Input β) (i : Fin n) :
    NamedFlat.Entry.inputEnv β record i.val =
      encodeValue Atoms (β.get i) (boundLookup T i (contextMap T β (packed β record)).2) := by
  rw [packed_field_proof β record i]
  exact NamedFlat.Entry.Record.inputEnv_field β record i

theorem table_arrow_proof (M : Model (κ := κ) Events Φ) (w : Witness g β R D)
    (h : w.Delimited) (ranked : Positional.Rank.check (FlatLetCase.localTargets g) = true)
    (record : Input β) :
    exitTree (List.ofFn D)
        (arrow M (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)))
        (packed β record) =
      region M.raw (NamedFlat.Entry.inputEnv β record) g.erase :=
  arrow_ordered M _ (packed β record) (NamedFlat.Entry.inputEnv β record) (agree record) _
    (SourceReadback.checkedTable_tree M w h ranked (NamedFlat.Entry.Record.field β record) _
      (NamedFlat.Entry.Record.inputEnv_field β record))

theorem readback_arrow_proof (M : Model (κ := κ) Events Φ) (w : Witness g β R D)
    (h : w.Delimited) (ranked : Positional.Rank.check (FlatLetCase.localTargets g) = true)
    (typed : g.HasType β R D) (record : Input β) (ambient : Env (Sigma Atoms)) :
    (exitTree (List.ofFn D)
        (arrow M (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)))
        (packed β record) >>= fun out => pure (FiniteCFG.packedTreeOutput out)) =
      region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry typed).code :=
  (arrow_packed M _ (packed β record) (NamedFlat.Entry.inputEnv β record) (agree record)).trans
    (SourceReadback.readback_packed M w h ranked typed record ambient)

end Table

/-! ## From the φ source to the arrow of the checked table -/

section Source

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping

variable {V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {n : Nat} {β : BoundCtx (Ty κ) n}

theorem source_arrow_proof (graph : Phi.Graph V K P.Instr) (table : Phi.Forward.Table V K)
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
            (packed β record) := by
  obtain ⟨code, w, h, ranked, elaborated, square⟩ := SourceReadback.source_readback graph table
    exits inputs types exitType C valid isClosed fragment covered certificate declared count shaped
  refine ⟨code, w, h, ranked, elaborated, fun M record => ?_⟩
  apply packed_injective
  rw [arrow_packed M _ (packed β record) (NamedFlat.Entry.inputEnv β record) (agree record),
    ← square M record]
  simp only [bind_assoc, pure_bind]

theorem source_arrow_infer_proof (graph : Phi.Graph V K P.Instr) (exits : List (Option K))
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
            (packed β record) := by
  obtain ⟨code, w, h, ranked, elaborated, square⟩ := SourceReadback.source_readback_infer graph
    exits inputs arrivals rank types exitType C inScope claims acyclic fragment covered
    certificate declared count shaped
  refine ⟨code, w, h, ranked, elaborated, fun M record => ?_⟩
  apply packed_injective
  rw [arrow_packed M _ (packed β record) (NamedFlat.Entry.inputEnv β record) (agree record),
    ← square M record]
  simp only [bind_assoc, pure_bind]

end Source

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceCategorical
