module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Exact.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Exact

open Silmaril.Isotope
open Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip (PacketClosed)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)} {blocks : Nat}
  {code : FiniteCFG P.Instr blocks I.exits.length I.slots}
  {registers : Registers V} {locals : Fin blocks → Nat → V} {internal : Fin blocks → K} {source : CFG V K P.Instr}

omit [DecidableEq V] in
theorem lower_attached_count (fields : K → List (V × Ty κ))
    (emitted : lowerWith registers locals I.names internal (fun i => I.exits[i]) code = some source) :
    (withLiveOut fields source).blocks.length = blocks := by
  simp only [lowerWith, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at emitted
  obtain ⟨_, _, _, _, rfl⟩ := emitted
  simp [withLiveOut, CFG.Cyclic.LiveOut.attach]

variable [DecidableEq P.Instr]

theorem accept_of_readback
    (emitted : lowerWith registers locals I.names internal (fun i => I.exits[i]) code = some source)
    (readback : elaborateAt (withLiveOut fields source) I.exits I.names blocks
      (lower_attached_count fields emitted) = some code) :
    lowerCheckedWith I fields registers locals internal code =
      some (Lowered.ofReadback source (lower_attached_count fields emitted) readback) := by
  have count := lower_attached_count fields emitted
  have closed : PacketClosed (withLiveOut fields source) :=
    elaborateAt_packetClosed _ _ _ count readback
  have atIndex (i : Fin (withLiveOut fields source).blocks.length) :
      (withLiveOut fields source).blocks[i].2.body.toRegion.fv ⊆
        {(withLiveOut fields source).blocks[i].2.param} :=
    closed _ (List.getElem_mem i.isLt)
  simp only [lowerCheckedWith, Option.bind_eq_bind, emitted, Option.bind_some, dite_eq_left count,
    dite_eq_left atIndex, dite_eq_left readback]
  rfl

theorem exact_of_accept
    (emitted : lowerWith registers locals I.names internal (fun i => I.exits[i]) code = some source)
    (accepted : (lowerCheckedWith I fields registers locals internal code).isSome = true) :
    elaborateAt (withLiveOut fields source) I.exits I.names blocks
      (lower_attached_count fields emitted) = some code := by
  have count := lower_attached_count fields emitted
  simp only [lowerCheckedWith, Option.bind_eq_bind, emitted, Option.bind_some, dite_eq_left count] at accepted
  split at accepted
  · split at accepted
    · assumption
    · contradiction
  · contradiction

theorem emitted_of_accept {output : Lowered I fields code}
    (accepted : lowerCheckedWith I fields registers locals internal code = some output) :
    lowerWith registers locals I.names internal (fun i => I.exits[i]) code = some output.source := by
  obtain ⟨actual, emitted, checked⟩ := Option.bind_eq_some_iff.mp accepted
  dsimp only at checked
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  split at checked <;> try contradiction
  exact emitted.trans (congrArg (fun result => some result.source) (Option.some.inj checked))

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Exact
