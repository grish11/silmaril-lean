module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.SourceReadback.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Flat.Fragment.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.Raw.SSA.Isotope.Morphism.CaseIter.Monadic
import Silmaril.Raw.SSA.Isotope.Morphism.Theory

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
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open LetCase.LocallyNameless (Derivation Equiv)
open Morphism.CaseSSA (erase)
open NamedFlat.Entry.Record (Input)

universe u v

variable {κ : Type (u + 1)} [AtomValues κ] [DecidableEq κ] {Φ : Type v} [HasTy Φ (Ty κ)]
  [HasEff Φ Bool] {Events : Type u → Type u}

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

local notation "Atoms" => AtomValues.carrier (κ := κ)
local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty κ))

/-- Native equality is sound for the weak tree of an erased term, in a
model whose typed and erased primitives are compatible, at an environment
that encodes a typed one. The only instructions that the equations treat
as pure are those of bottom effect, and the typed model interprets those
as functions. -/
theorem term_eq_of_equiv_proof (M : Model (κ := κ) Events Φ) {n : Nat} {β : BoundCtx (Ty κ) n}
    {a b : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty κ} (h : Equiv false Γ₀ β a b A)
    (da : Derivation Φ Γ₀ β a A) (db : Derivation Φ Γ₀ β b A)
    (ρ : BoundEnv (Ty.denote Atoms) β) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val = encodeValue Atoms (β.get i) (ρ i)) :
    LambdaSSA.Semantics.Interaction.term M.raw env (erase a) =
      LambdaSSA.Semantics.Interaction.term M.raw env (erase b) := by
  let _ := M.instructions
  let typed : Isotope.Semantics.InstructionModel (Ty.denote Atoms) Φ (LambdaSSA.Semantics.Interaction.Typed.ModelTree Events) :=
    ⟨fun f x => InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := LambdaSSA.Semantics.Interaction.Typed.ModelTree Events) f x⟩
  have pureM : Isotope.Semantics.InstructionModel.RespectsPure (ε := Bool) typed :=
    fun f bottom => ⟨InstructionModel.denotePure (τ := Ty κ) (ε := Bool)
      (m := LambdaSSA.Semantics.Interaction.Typed.ModelTree Events) f bottom, fun x =>
      InstructionModel.denote_pure (τ := Ty κ) (ε := Bool)
        (m := LambdaSSA.Semantics.Interaction.Typed.ModelTree Events) f bottom x⟩
  have sound := LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil.{u + 1, u + 1} (ε := Bool)
    Atoms typed
    pureM (.equiv (Silmaril.Isotope.Morphism.CaseIter.embed_equiv h)) (Silmaril.Isotope.Morphism.CaseIter.derivation da)
    (Silmaril.Isotope.Morphism.CaseIter.derivation db) ρ
  simp only [Silmaril.Isotope.Morphism.CaseIter.denote_derivation] at sound
  rw [← FlatLetCase.denote_tree typed M.raw M.compatible da ρ env agree,
    ← FlatLetCase.denote_tree typed M.raw M.compatible db ρ env agree, sound]

/-! ## The packed program of a flat graph -/

section Packed

variable {blocks exits n : Nat} {β : BoundCtx (Ty κ) n} {R : Fin blocks → Ty κ}
  {D : Fin exits → Ty κ} {g : FiniteCFG Φ blocks exits n}

omit [DecidableEq κ] in
/-- The typed packed program of a flat graph, on the packed input record,
runs as the graph does on the decoded captures. -/
theorem packed_program_proof (M : Model (κ := κ) Events Φ) (typed : g.HasType β R D)
    (record : Input β) (ambient : Env (Sigma Atoms)) :
    region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry typed).code =
      (region M.raw (NamedFlat.Entry.inputEnv β record) g.erase >>= fun p =>
        pure (FiniteCFG.packedTreeOutput p)) := by
  change region M.raw (extend ambient (encodeValue Atoms _ record))
    ((FiniteCFG.packedExecutionRegion typed).packInputsDestructure β.toList) = _
  rw [← NamedFlat.Entry.inputEnv_packet β record,
    NamedFlat.Capture.packed_context_tree M.raw typed ambient]

end Packed

/-! ## The checked table of a flat graph -/

section Table

variable {size exits n : Nat} {β : BoundCtx (Ty κ) n} {R : Fin (size + 1) → Ty κ}
  {D : Fin exits → Ty κ} {g : FiniteCFG Φ (size + 1) exits n}

/-- The readback of the checked table of a flat graph in the fragment has
the weak tree of the flat graph, with the exit packed into the value. -/
theorem checkedTable_tree_proof (M : Model (κ := κ) Events Φ) (w : Witness g β R D)
    (h : w.Delimited) (ranked : Positional.Rank.check (FlatLetCase.localTargets g) = true)
    (ρ : BoundEnv (Ty.denote Atoms) β) (env : Env (Sigma Atoms))
    (agree : ∀ i, env i.val = encodeValue Atoms (β.get i) (ρ i)) :
    LambdaSSA.Semantics.Interaction.term M.raw env
        (erase (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)).toLetCase.1) =
      (region M.raw env g.erase >>= fun out => pure (Region.packedExitValue out.1 out.2)) := by
  rw [← FlatLetCase.compile_tree M.raw w ranked env]
  exact (term_eq_of_equiv_proof M
    (FlatLetCase.Witness.checkedTable_readback false w h ranked
      (FlatLetCase.Witness.table_check w h ranked))
    (FlatLetCase.compile w ranked).toLetCase.2
    (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)).toLetCase.2 ρ env agree).symm

/-- The readback of the checked table and the typed packed program of the
same flat graph have the same weak tree, up to the exit adapter: the
readback returns the packed exit value, and the packed program returns
it at its single label. -/
theorem readback_packed_proof (M : Model (κ := κ) Events Φ) (w : Witness g β R D)
    (h : w.Delimited) (ranked : Positional.Rank.check (FlatLetCase.localTargets g) = true)
    (typed : g.HasType β R D) (record : Input β) (ambient : Env (Sigma Atoms)) :
    (LambdaSSA.Semantics.Interaction.term M.raw (NamedFlat.Entry.inputEnv β record)
        (erase (w.checkedTable h (FlatLetCase.Witness.table_check w h ranked)).toLetCase.1) >>=
        fun value => pure (0, value)) =
      region M.raw (extend ambient (encodeValue Atoms _ record)) (Program.ofCFGEntry typed).code := by
  rw [packed_program_proof M typed record ambient,
    checkedTable_tree_proof M w h ranked (NamedFlat.Entry.Record.field β record) _
      (NamedFlat.Entry.Record.inputEnv_field β record)]
  simp only [bind_assoc, pure_bind]
  rfl

end Table

/-! ## The elaborated graph at a literal count of blocks -/

section Recount

variable {a b exits n : Nat}

omit [AtomValues κ] [DecidableEq κ] [HasTy Φ (Ty κ)] [HasEff Φ Bool] in
theorem recount_erase_proof (count : a = b) (g : FiniteCFG Φ a exits n) :
    (recount count g).erase = g.erase := by
  subst count
  rfl

omit [AtomValues κ] [DecidableEq κ] [HasEff Φ Bool] in
theorem recount_typed_proof (count : a = b) {g : FiniteCFG Φ a exits n} {β : BoundCtx (Ty κ) n}
    {R : Fin a → Ty κ} {D : Fin exits → Ty κ} (typed : g.HasType β R D) :
    (recount count g).HasType β (fun i => R (Fin.cast count.symm i)) D := by
  subst count
  exact typed

end Recount

/-! ## From the φ source to the readback of the checked table -/

section Source

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceTyping

variable {V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {n : Nat} {β : BoundCtx (Ty κ) n}

/-- The φ run of the original graph is the weak tree of the readback of
the checked table of the elaborated graph, for any witness of the
elaborated graph in the fragment. -/
theorem source_readback_proof (graph : Phi.Graph V K P.Instr) (table : Phi.Forward.Table V K)
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
            fun value => pure (0, value)) := by
  obtain ⟨code, typed, elaborated, square⟩ := SourceSemantics.source_square graph table exits
    inputs types exitType C valid isClosed fragment covered certificate declared
  rw [elaborated] at shaped
  simp only [Option.all_some, Bool.and_eq_true] at shaped
  have recounted := recount_typed_proof count typed
  obtain ⟨w⟩ := FlatLetCase.witness_nonempty recounted
  have h := FlatLetCase.Witness.delimited_of_shape w shaped.1
  refine ⟨code, w, h, shaped.2, elaborated, fun M record => ?_⟩
  rw [square M record (fun _ => .unit), packed_program_proof M typed record,
    ← recount_erase_proof count code, ← packed_program_proof M recounted record (fun _ => .unit)]
  exact (readback_packed_proof M w h shaped.2 recounted record _).symm

/-- The same from checks on the original graph only, with the inferred
forwarding table. -/
theorem source_readback_infer_proof (graph : Phi.Graph V K P.Instr) (exits : List (Option K))
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
            fun value => pure (0, value)) := by
  have labels : (graph.blocks.map Prod.fst).Nodup := by
    have checks := inScope
    simp only [Phi.OrderedExits.check, Phi.GlobalSSA.check, Phi.Graph.check, Bool.and_eq_true,
      decide_eq_true_eq] at checks
    have distinct := checks.2.1.1.1
    simpa [Phi.OrderedExits.forScope, List.map_map, Function.comp_def] using distinct
  exact source_readback_proof graph _ exits inputs types exitType C
    (Phi.Forward.check_infer graph exits inputs labels)
    (Phi.Forward.closed_infer_of_ranked graph exits inputs arrivals rank inScope claims acyclic)
    fragment covered certificate declared count shaped

end Source

end Silmaril.Isotope.Bridge.NamedFlat.Phi.SourceReadback
