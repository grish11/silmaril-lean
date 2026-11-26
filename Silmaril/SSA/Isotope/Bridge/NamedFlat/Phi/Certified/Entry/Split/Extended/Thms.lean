module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Extended.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Extended

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Elgot.ITree (TraceLE)
open NamedFlat.Entry.Record (Input)
open PureCapture.Local.Split (Generated extendedTypes)

universe u v

variable {κ V W K J : Type (u + 1)} {n : Nat} {β : BoundCtx (Ty κ) n}
  {I : Captures V β} {D : Fin 1 → Ty κ}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {Events : Type u → Type u}

local notation "C" => AtomValues.carrier (κ := κ)

variable (original : Admitted P I K D) (plan : Plan V W K J)
  (result : Generated plan original.source original.inputs I.names β D)
  (layout : ExtendedLayout plan I result.extra) (M : Model (κ := κ) Events P.Instr)

/-- Packed execution at a supplied extended record equals the original
packed execution at the projection of that record to its retained slots. -/
theorem split_packed_reindex (record : Input (extendedTypes β result.extra)) (ambient : Env (Sigma C)) :
    original.observePacked M (retainedRecord β result.extra record) ambient =
      (original.ofExtended plan result layout).observePacked M record ambient :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.packed_reindex
    original plan result layout M record ambient

/-- The same record projection relates the admitted named observations. -/
theorem split_named_reindex (record : Input (extendedTypes β result.extra)) :
    original.toSSA.observe M (retainedRecord β result.extra record) =
      (original.ofExtended plan result layout).toSSA.observe M record :=
  (NamedFlat.Entry.SSA.observe_tree M original.toSSA _ (fun _ => .unit)).trans
    ((split_packed_reindex original plan result layout M record (fun _ => .unit)).trans
      (NamedFlat.Entry.SSA.observe_tree M (original.ofExtended plan result layout).toSSA
        record (fun _ => .unit)).symm)

/-- Both directions of the trace comparison hold on related records, in the
named runner and in its packed translation. -/
theorem split_related_satisfies
    (left : Input β) (right : Input (extendedTypes β result.extra))
    (related : retainedRecord β result.extra right = left) (ambient : Env (Sigma C)) :
    (TraceLE (original.toSSA.observe M left) ((original.ofExtended plan result layout).toSSA.observe M right) ∧
      TraceLE ((original.ofExtended plan result layout).toSSA.observe M right) (original.toSSA.observe M left)) ∧
    (TraceLE (original.observePacked M left ambient)
        ((original.ofExtended plan result layout).observePacked M right ambient) ∧
      TraceLE ((original.ofExtended plan result layout).observePacked M right ambient)
        (original.observePacked M left ambient)) := by
  rw [← related, split_named_reindex original plan result layout M right,
    split_packed_reindex original plan result layout M right ambient]
  exact ⟨⟨TraceLE.refl _, TraceLE.refl _⟩, ⟨TraceLE.refl _, TraceLE.refl _⟩⟩

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
