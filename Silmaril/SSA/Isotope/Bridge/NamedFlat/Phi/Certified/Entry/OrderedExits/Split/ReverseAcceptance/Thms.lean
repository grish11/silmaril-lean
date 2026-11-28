module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Admission.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Exact.Thms

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Registers lower withLiveOut lower_attached_count lowerChecked_iff_readback)

universe u v
variable {κ V W Reg K : Type (u + 1)}
  [DecidableEq V] [DecidableEq W] [DecidableEq Reg] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} [DecidableEq P.Instr]
  {I : NamedFlat.Entry.Interface κ Reg (Option K)} {fields : Option K → List (Reg × Ty κ)}
  {C : Captures V I.context} {plan : Plan V W K K} {a : Admission P I fields C}

/-- After the ordinary reverse lowerer emits a table for the generated
split, exact elaboration with the ordered live-outs attached suffices for
reverse acceptance. The count follows from emission and closure from readback. -/
theorem GeneratedSplit.reverseChecked_iff_readback (split : GeneratedSplit plan a)
    (registers : Registers Reg)
    (internal : Fin (Versioning.compile (Phi.OrderedExits.lower split.target.source)).blocks.length → Option K)
    {source : CFG Reg (Option K) P.Instr}
    (emitted : lower registers I.names internal (fun i => I.exits[i]) split.target.code = some source) :
    (split.target.reverseChecked registers internal).isSome = true ↔
      NamedFlat.elaborateAt (withLiveOut fields source) I.exits I.names _
        (lower_attached_count fields emitted) = some split.target.code :=
  lowerChecked_iff_readback emitted

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
