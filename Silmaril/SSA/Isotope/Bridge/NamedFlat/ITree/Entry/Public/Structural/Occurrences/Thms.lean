module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.NamedSSA.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction (region)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source : CFG V K F}
  {exits : List K} {fields : K → List V} {outputs : Fin exits.length → PacketType}
  {ty : PacketType} (entry : StructuralEntry signature source exits fields ty outputs)

theorem StructuralEntry.occurrenceNames_injective : Function.Injective entry.occurrenceNames :=
  fun _ _ same => Fin.ext (congrArg ULift.down same)

/-- Each checked occurrence receives its source register's value with its
own exact type. Repeated reads can name different slots in this context. -/
theorem StructuralEntry.occurrenceStore_typed (initial : V → Value Atom) (packet : Denote ty)
    (checked : entry.seed? initial = some packet) (i : Fin entry.footprint.length) :
    entry.occurrenceStore packet (entry.occurrenceNames i) = initial entry.footprint[i.val].1 ∧
      ∃ v : Denote (entry.occurrenceContext.get i),
        entry.occurrenceStore packet (entry.occurrenceNames i) =
          PacketType.encode (entry.occurrenceContext.get i) v :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.slots_typed
    entry initial packet checked i

/-- The occurrence jump assembles the identical packet at the original
public label. Packet closure makes the change of entry store invisible
to all of the unchanged rows. -/
theorem StructuralEntry.observeOccurrences_eq_public (packet : Denote ty) :
    entry.observeOccurrences packet =
      (entry.program.observe 0 packet >>= fun out => pure (FiniteCFG.packedTreeOutput out)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.observe_eq_public entry packet

/-- Successful elaboration and exact typing identify the occurrence runner
with its admitted flat code at the assembled occurrence store. -/
theorem OccurrenceAdmission.observe_eq_elaborated (admitted : OccurrenceAdmission entry) (packet : Denote ty) :
    entry.observeOccurrences packet =
      (region signature.primitive (fun i => entry.occurrenceStore packet ⟨i⟩) admitted.code.erase >>=
        fun out => pure (FiniteCFG.packedTreeOutput out)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.observe_eq_elaborated entry admitted packet

/-- A checked source seed relates the original lexical SSA runner and the
occurrence-entry named SSA runner at their actual stores. -/
theorem StructuralEntry.observeVersioned_eq_occurrences (initial : V → Value Atom) (packet : Denote ty)
    (checked : entry.seed? initial = some packet) :
    entry.observeVersioned initial = entry.observeOccurrences packet :=
  (entry.observeVersioned_eq_public initial packet checked).trans (entry.observeOccurrences_eq_public packet).symm

/-- The same diagram for the original mutable runner, keeping the ordered
exit and selected live-outs. -/
theorem StructuralEntry.observeRaw_eq_occurrences (initial : V → Value Atom) (packet : Denote ty)
    (checked : entry.seed? initial = some packet) :
    LiveOut.observeRaw signature.primitive exits fields source initial = entry.observeOccurrences packet :=
  (entry.observeVersioned_eq initial).symm.trans (entry.observeVersioned_eq_occurrences initial packet checked)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
