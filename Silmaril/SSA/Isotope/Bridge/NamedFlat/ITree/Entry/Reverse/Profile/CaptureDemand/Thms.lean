module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.CaptureDemand.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.CaptureDemand

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v w

section Analysis

variable {V K : Type w} {F : Type v} {n : Nat} [DecidableEq V] [DecidableEq K]
  (graph : CFG V K F) (names : Fin n → V)

/-- Backward analysis includes the reads of each row and the requirements of its successors. -/
theorem infer_closed : Closed graph names (infer graph names) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand.infer_closed graph names

/-- Every assignment satisfying the local read and transfer constraints contains the inferred slots. -/
theorem infer_le {live : Fin graph.blocks.length → Finset (Fin n)} (closed : Closed graph names live) :
    infer graph names ≤ live :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand.infer_le graph names closed

/-- Ordering retains precisely the required slots present in the supplied entry list. -/
theorem mem_ordered (entry : List (Fin n)) (i : Fin graph.blocks.length) (slot : Fin n) :
    slot ∈ ordered graph names entry i ↔ slot ∈ entry ∧ slot ∈ infer graph names i := by
  simp [ordered]

/-- A demanded slot shadowed by its block argument obstructs every closed
plan that carries the unchanged entry values. -/
theorem noShadow_iff :
    (∃ live, Closed graph names live ∧ NoShadow graph names live) ↔ NoShadow graph names (infer graph names) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand.noShadow_iff graph names

/-- For certified packet-local source, all useful reads already come from
the original argument. Every inferred extra capture record is empty. -/
theorem infer_empty_of_packetClosed (closed : RoundTrip.PacketClosed graph) :
    infer graph names = fun _ => ∅ :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand.infer_empty_of_packetClosed graph names closed

end Analysis

section Reference

variable {κ K : Type (u + 1)} {n blocks : Nat} [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : LambdaSSA.FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "versioned" => Versioning.compile attached

/-- When all actual saved registers are in range, the reference lists
recover exactly the installed slots in order. -/
theorem reference_layout (within : a.SavesCaptures) (i : Fin (versioned).blocks.length) :
    a.savedRegisters i = (referenceLayouts a i).map (fun j => (⟨j.val⟩ : Register)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand.reference_layout a within i

/-- Reference lists project the same ordered entry support at every row. -/
theorem reference_projection (i : Fin (versioned).blocks.length) :
    List.Sublist (referenceLayouts a i) (referenceEntry a) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand.reference_projection a i

/-- The inferred ordered list agrees with the actual compiler exactly when
every row's parameter exhausts the global support. Packet closure makes
the inferred list empty, while the existing compiler may save more. -/
theorem ordered_installed_iff (entry : List (Fin n)) :
    (∀ i, a.savedRegisters i =
      (ordered attached (fun j : Fin n => (⟨j.val⟩ : Register)) entry
        (Fin.cast (List.length_map _) i)).map (fun j => (⟨j.val⟩ : Register))) ↔
    ∀ i : Fin (versioned).blocks.length, ∀ reg ∈ Versioning.registers attached,
      reg = (attached).blocks[Fin.cast (List.length_map _) i].2.param :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand.ordered_installed_iff a entry

/-- Re-admit using layouts recovered from the actual compiler. The
certificate uses the original entry types, original packet types and
ordered exits. No post-versioning readback or typing witness is supplied. -/
@[expose] def admitReference [DecidableEq κ] (R : Fin blocks → Ty κ) :
    Option (LiveOut.Admission P (numberedInterface context exits external) fields a.source) :=
  if ready : referenceReady a R = true then
    have gates : a.SavesCaptures ∧ Straight.keepsEntryCaptures a (referenceEntry a) = true ∧
        Straight.checksCaptureEdges a (referenceLayouts a) = true ∧ Straight.checks a R = true := by
      simpa [referenceReady, and_assoc] using ready
    some (Straight.admitWithProjections a R (referenceEntry a) (referenceLayouts a)
      (reference_layout a gates.1) (reference_projection a) gates.2.1 gates.2.2.1 gates.2.2.2)
  else none

end Reference

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.CaptureDemand
