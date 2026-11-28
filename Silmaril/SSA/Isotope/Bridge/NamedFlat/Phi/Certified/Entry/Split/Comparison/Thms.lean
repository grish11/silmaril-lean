module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Comparison.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Extended.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Record.Thms

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (Tree)
open NamedFlat.Entry.Record (Input reindex reindex_id reindex_comp)
open PureCapture.Local.Split (Generated originalSlots)

universe u v

variable {κ V W X K J H : Type (u + 1)} {n m k : Nat}
  {β : BoundCtx (Ty κ) n} {γ : BoundCtx (Ty κ) m} {δ : BoundCtx (Ty κ) k}
  {I : Captures V β} {L : Captures W γ} {N : Captures X δ} {D : Fin 1 → Ty κ}
  [DecidableEq V] [DecidableEq W] [DecidableEq X]
  [DecidableEq K] [DecidableEq J] [DecidableEq H] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {Events : Type u → Type u}
  {a : Admitted P I K D} {b : Admitted P L J D} {c : Admitted P N H D}

local notation "C" => AtomValues.carrier (κ := κ)
local notation "Observation" => Tree Events (Transfer (Sigma C))

/-- A generated split compares its admitted endpoints along its retained slot map. -/
def EntryComparison.ofSplit (a : Admitted P I K D) (plan : Plan V W K J)
    (result : Generated plan a.source a.inputs I.names β D)
    (layout : ExtendedLayout plan I result.extra) :
    EntryComparison Events a (a.ofExtended plan result layout) :=
  ⟨originalSlots β result.extra, split_packed_reindex a plan result layout⟩

def EntryComparison.id (a : Admitted P I K D) : EntryComparison Events a a :=
  ⟨.id β, fun M record ambient => congrArg (fun r => a.observePacked M r ambient) (reindex_id β record)⟩

/-- Compose comparisons at their shared admitted table and compose their
checked slot maps. Records are supplied at the final table. -/
def EntryComparison.comp (first : EntryComparison Events a b) (second : EntryComparison Events b c) :
    EntryComparison Events a c :=
  ⟨first.slots.comp second.slots, fun M record ambient =>
    (congrArg (fun r => a.observePacked M r ambient) (reindex_comp first.slots second.slots record)).trans
      ((first.packed M (reindex second.slots record) ambient).trans (second.packed M record ambient))⟩

/-- The observation law also holds for the actual admitted named runner. -/
theorem EntryComparison.named (comparison : EntryComparison Events a b)
    (M : Model (κ := κ) Events P.Instr) (record : Input γ) :
    a.toSSA.observe M (reindex comparison.slots record) = b.toSSA.observe M record :=
  (NamedFlat.Entry.SSA.observe_tree M a.toSSA _ (fun _ => .unit)).trans
    ((comparison.packed M record (fun _ => .unit)).trans
      (NamedFlat.Entry.SSA.observe_tree M b.toSSA record (fun _ => .unit)).symm)

/-- Pull back predicates on the named and packed observations together at a
supplied target record. Either argument of trace inclusion can be fixed to
obtain a directed comparison in that orientation. -/
theorem EntryComparison.satisfies_iff (comparison : EntryComparison Events a b)
    (M : Model (κ := κ) Events P.Instr) (record : Input γ) (ambient : Env (Sigma C))
    (named packed : Observation → Prop) :
    (named (b.toSSA.observe M record) ∧ packed (b.observePacked M record ambient)) ↔
      (named (a.toSSA.observe M (reindex comparison.slots record)) ∧
        packed (a.observePacked M (reindex comparison.slots record) ambient)) := by
  rw [comparison.named M record, comparison.packed M record ambient]

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
