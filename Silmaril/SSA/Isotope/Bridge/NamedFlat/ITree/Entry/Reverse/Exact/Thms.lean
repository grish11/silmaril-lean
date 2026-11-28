module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Exact.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Exact

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)} {blocks : Nat}
  {code : FiniteCFG P.Instr blocks I.exits.length I.slots}
  {registers : Registers V} {internal : Fin blocks → K} {source : CFG V K P.Instr}

omit [DecidableEq V] in
/-- Successful emission fixes the attached block count. -/
theorem lower_attached_count (fields : K → List (V × Ty κ))
    (emitted : lower registers I.names internal (fun i => I.exits[i]) code = some source) :
    (withLiveOut fields source).blocks.length = blocks :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Exact.lower_attached_count fields emitted

variable [DecidableEq P.Instr]

/-- Exact readback of the emitted table constructs the result of the
ordinary reverse checker, with block count and packet closure derived. -/
theorem lowerChecked_eq_of_readback
    (emitted : lower registers I.names internal (fun i => I.exits[i]) code = some source)
    (readback : elaborateAt (withLiveOut fields source) I.exits I.names blocks
      (lower_attached_count fields emitted) = some code) :
    lowerChecked I fields registers internal code =
      some (Lowered.ofReadback source (lower_attached_count fields emitted) readback) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Exact.accept_of_readback emitted readback

/-- Once emission succeeds, exact scoped readback is the remaining
acceptance condition. -/
theorem lowerChecked_iff_readback
    (emitted : lower registers I.names internal (fun i => I.exits[i]) code = some source) :
    (lowerChecked I fields registers internal code).isSome = true ↔
      elaborateAt (withLiveOut fields source) I.exits I.names blocks
        (lower_attached_count fields emitted) = some code :=
  ⟨Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Exact.exact_of_accept emitted,
    fun readback => by rw [lowerChecked_eq_of_readback emitted readback]; rfl⟩

/-- The certificate returned by the exact checker names the actual RTL
table emitted at that allocation. -/
theorem lowerChecked_emitted {output : Lowered I fields code}
    (accepted : lowerChecked I fields registers internal code = some output) :
    lower registers I.names internal (fun i => I.exits[i]) code = some output.source :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Exact.emitted_of_accept accepted

variable {locals : Fin blocks → Nat → V}

/-- The certificate from the opt-in body-local checker names its actual
emission using the shared packet parameter. -/
theorem lowerCheckedWith_emitted {output : Lowered I fields code}
    (accepted : lowerCheckedWith I fields registers locals internal code = some output) :
    lowerWith registers locals I.names internal (fun i => I.exits[i]) code = some output.source :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Exact.emitted_of_accept accepted

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
