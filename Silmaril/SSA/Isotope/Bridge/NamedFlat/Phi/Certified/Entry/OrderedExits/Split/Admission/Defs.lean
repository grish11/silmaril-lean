module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Arrival.Thms

/-! # Generate ordered typed φ admission from the original entry interface -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits (checkExits forScope lower)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
  (ProfileCandidateFor profileCandidateFor splitCertificate)

universe u v
variable {κ V W Reg K : Type (u + 1)} [DecidableEq V] [DecidableEq W] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context}

/-- Reconstruct the split profile in the actual ordered lowering's block and
packet order. The extra list reports version-zero captures absent from the
renamed original interface. Its entries give names and proposed types. -/
def Admission.splitProfile (a : Admission P I fields C) (plan : Plan V W K K) :
    Option (ProfileCandidateFor W κ I.slots
      (Versioning.compile (lower (plan.rewrite a.source))).blocks.length) :=
  profileCandidateFor plan a.source (lower a.source) (lower (plan.rewrite a.source)) C.names a.internal

/-- Result of the fixed-record generator. Static φ inputs and arrival claims
are transported from the source. Entry captures retain their types and
positions under the register equivalence. -/
structure GeneratedSplit (plan : Plan V W K K) (a : Admission P I fields C) where
  target : Admission P I fields (C.rename plan.register)
  checked : CheckedSplit plan a.source target.source
  exits : I.exits.map (Option.map plan.label) = I.exits
  inputs : target.inputs = a.inputs.map plan.register
  arrivals : target.arrivals = splitCertificate plan a.source a.arrivals

/-- Generate the graph, static inputs, arrivals and packet profile from the
original admission. Check target shape and actual named typing at the same
record. A missing capture requires a different input interface. -/
def Admission.generateSplit [DecidableEq κ] (a : Admission P I fields C) (plan : Plan V W K K) :
    Option (GeneratedSplit plan a) :=
  let target := plan.rewrite a.source
  if exits : I.exits.map (Option.map plan.label) = I.exits then
    if edge : (a.source.blocks.lookup plan.header).isSome = true ∧ plan.hasEdge a.source = true then
      if shape : checkExits target I.exits = true ∧ (forScope target I.exits).check = true then
        (a.splitProfile plan).bind fun candidate =>
          if candidate.extra.isEmpty then
            let arrivals := splitCertificate plan a.source a.arrivals
            let arrived := split_check plan a.source I.exits a.inputs a.arrivals a.checked exits
              edge.1 edge.2 shape.1 shape.2
            (NamedFlat.compileTyped (lower target) I.exits (C.rename plan.register).names
              I.context candidate.blocks (NamedFlat.Entry.LiveOut.exitInterface I fields).external).map fun code =>
                ⟨⟨target, a.inputs.map plan.register, arrivals, arrived, candidate.blocks,
                    code.val, code.property.1, code.property.2⟩,
                  ⟨edge.1, edge.2, rfl⟩, exits, rfl, rfl⟩
          else none
      else none
    else none
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
