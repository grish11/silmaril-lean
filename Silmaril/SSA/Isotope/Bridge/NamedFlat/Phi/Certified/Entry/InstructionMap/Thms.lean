module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.InstructionMap.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Comparison.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.InstructionMap

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open CategoryTheory
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (Tree)
open NamedFlat.Entry.Record (Input reindex)

universe u v
variable {κ V W X K J H : Type (u + 1)} {n m k : Nat}
  {β : BoundCtx (Ty κ) n} {γ : BoundCtx (Ty κ) m} {δ : BoundCtx (Ty κ) k}
  {I : Captures V β} {L : Captures W γ} {N : Captures X δ} {D : Fin 1 → Ty κ}
  [DecidableEq V] [DecidableEq K] [DecidableEq W] [DecidableEq J] [DecidableEq X] [DecidableEq H]
  {P Q : FlatInstitution.Signature.{u, v} κ}
  {a : Admitted P I K D} {b : Admitted P L J D} {c : Admitted P N H D}

theorem Admitted.toSSA_ofSSA (source : Phi.Graph V K P.Instr) (inputs : List V)
    (wf : Phi.GlobalSSA.WellFormed source inputs)
    (table : NamedFlat.Entry.SSA P (I.named K D).version)
    (lowered : table.source = Versioning.compile (Phi.lower source)) :
    (Admitted.ofSSA source inputs wf table lowered).toSSA = table :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.toSSA_ofSSA source inputs wf table lowered

/-- The translated written table and its exact profile are the ordinary
named typed-entry map on the original certificate. -/
theorem Admitted.toSSA_map (a : Admitted P I K D) (g : P ⟶ Q) :
    (a.map g).toSSA = a.toSSA.map g :=
  toSSA_ofSSA _ _ _ _ _

variable [AtomValues κ] {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)
local notation "Observation" => Tree Events (Transfer (Sigma C))

theorem Admitted.observe_named_map (a : Admitted P I K D) (g : P ⟶ Q)
    (M : Model (κ := κ) Events Q.Instr) (record : Input β) :
    (a.map g).toSSA.observe M record = a.toSSA.observe (FlatInstitution.reduct Events g M) record := by
  rw [a.toSSA_map]
  exact Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.named_observe_map a g M record

/-- The same reduct square for the independent predecessor-row evaluator. -/
theorem Admitted.observe_map (a : Admitted P I K D) (g : P ⟶ Q)
    (M : Model (κ := κ) Events Q.Instr) (record : Input β) :
    (a.map g).observe M record = a.observe (FlatInstitution.reduct Events g M) record :=
  ((a.map g).observe_toSSA M record).symm.trans
    ((a.observe_named_map g M record).trans (a.observe_toSSA _ record))

theorem Admitted.observePacked_map (a : Admitted P I K D) (g : P ⟶ Q)
    (M : Model (κ := κ) Events Q.Instr) (record : Input β) (ambient : Env (Sigma C)) :
    (a.map g).observePacked M record ambient =
      a.observePacked (FlatInstitution.reduct Events g M) record ambient :=
  (NamedFlat.Entry.SSA.observe_tree M (a.map g).toSSA record ambient).symm.trans
    ((a.observe_named_map g M record).trans
      (NamedFlat.Entry.SSA.observe_tree (FlatInstitution.reduct Events g M) a.toSSA record ambient))

/-- Relabel the admitted endpoints and retain their checked projection. -/
def EntryComparison.map (comparison : EntryComparison Events a b) (g : P ⟶ Q) :
    EntryComparison Events (a.map g) (b.map g) :=
  ⟨comparison.slots, fun M record ambient =>
    ((a.observePacked_map g M _ ambient).trans
      (comparison.packed (FlatInstitution.reduct Events g M) record ambient)).trans
      (b.observePacked_map g M record ambient).symm⟩

@[simp] theorem EntryComparison.map_slots (comparison : EntryComparison Events a b) (g : P ⟶ Q) :
    (comparison.map g).slots = comparison.slots := rfl

theorem EntryComparison.map_comp (first : EntryComparison Events a b) (second : EntryComparison Events b c)
    (g : P ⟶ Q) :
    (first.comp second).map g = (first.map g).comp (second.map g) := rfl

/-- Compare at the final supplied record and at its checked projection.
Predicates on either orientation of the named and packed observations
transport between the relabelled tables and the reduct. -/
theorem EntryComparison.satisfies_map_iff (comparison : EntryComparison Events a b) (g : P ⟶ Q)
    (M : Model (κ := κ) Events Q.Instr) (record : Input γ) (ambient : Env (Sigma C))
    (named packed : Observation → Observation → Prop) :
    let input := reindex comparison.slots record
    let reduct := FlatInstitution.reduct Events g M
    (named ((a.map g).toSSA.observe M input) ((b.map g).toSSA.observe M record) ∧
      packed ((a.map g).observePacked M input ambient) ((b.map g).observePacked M record ambient)) ↔
    (named (a.toSSA.observe reduct input) (b.toSSA.observe reduct record) ∧
      packed (a.observePacked reduct input ambient) (b.observePacked reduct record ambient)) := by
  dsimp only
  rw [a.observe_named_map, b.observe_named_map, a.observePacked_map, b.observePacked_map]

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
