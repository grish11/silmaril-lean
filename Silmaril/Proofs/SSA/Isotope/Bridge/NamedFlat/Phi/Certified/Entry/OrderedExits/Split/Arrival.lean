module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Split.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA (Certificate)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
  (splitCertificate splitCertificate_check)

universe v w
variable {V W K : Type w} {F : Type v} [DecidableEq V] [DecidableEq W] [DecidableEq K]

theorem split_check (plan : Plan V W K K) (graph : Graph V K F) (exits : List (Option K))
    (inputs : List V) (arrivals : Certificate V K) (accepted : check graph exits inputs arrivals = true)
    (aligned : exits.map (Option.map plan.label) = exits)
    (header : (graph.blocks.lookup plan.header).isSome = true) (edge : plan.hasEdge graph = true)
    (partition : checkExits (plan.rewrite graph) exits = true)
    (normalized : (forScope (plan.rewrite graph) exits).check = true) :
    check (plan.rewrite graph) exits (inputs.map plan.register)
      (splitCertificate plan graph arrivals) = true := by
  simp only [check, Bool.and_eq_true] at accepted ⊢
  obtain ⟨sourcePartition, sourceChecked⟩ := accepted
  have internal := header_not_exit graph exits sourcePartition header
  have scope := forScope_rewrite plan graph exits internal
  rw [aligned] at scope
  have scopedEdge : plan.hasEdge (forScope graph exits) = true :=
    (hasEdge_forScope plan graph exits internal).trans edge
  have arrived := splitCertificate_check (plan := plan) sourceChecked scopedEdge (scope ▸ normalized)
  refine ⟨partition, ?_⟩
  rw [scope]
  simpa only [splitCertificate, edgeReads_forScope] using arrived

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split
