module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Split.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Arrival

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA (Certificate)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits (checkExits forScope)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split (splitCertificate)

universe v w
variable {V W K : Type w} {F : Type v} [DecidableEq V] [DecidableEq W] [DecidableEq K]

/-- Transport an accepted arrival table through the ordered split, using the
renamed input definitions and the forwarding claim from the original table.
The target exit partition and normalized predecessor rows can be checked
without a target arrival table. -/
theorem split_check (plan : Plan V W K K) (graph : Graph V K F) (exits : List (Option K))
    (inputs : List V) (arrivals : Certificate V K) (accepted : Phi.OrderedExits.check graph exits inputs arrivals = true)
    (aligned : exits.map (Option.map plan.label) = exits)
    (header : (graph.blocks.lookup plan.header).isSome = true) (edge : plan.hasEdge graph = true)
    (partition : checkExits (plan.rewrite graph) exits = true)
    (normalized : (forScope (plan.rewrite graph) exits).check = true) :
    Phi.OrderedExits.check (plan.rewrite graph) exits (inputs.map plan.register)
      (splitCertificate plan graph arrivals) = true :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.split_check
    plan graph exits inputs arrivals accepted aligned header edge partition normalized

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
