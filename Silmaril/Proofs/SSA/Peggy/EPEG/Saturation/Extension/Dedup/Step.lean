module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Checker
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms
import Silmaril.SSA.PEG.Rules.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n k l : Nat}
variable {small : State P params results n l} {large : State P params results k l}
variable {site rhs : Fin n} {zero : P [] .count}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}

theorem prefix_refl (s : Output P params results l) : Prefix s s :=
  ⟨Embedding.refl s.2, fun i => congrArg Fin.val (Embedding.refl_address s.2 i)⟩

theorem prefix_trans {a b c : Output P params results l} (ab : Prefix a b) (bc : Prefix b c) : Prefix a c := by
  obtain ⟨e, first⟩ := ab
  obtain ⟨f, second⟩ := bc
  exact ⟨e.trans f, fun i => by rw [Embedding.trans_address, second, first]⟩

private theorem rhs_transport (e : Embedding small large) (found : ZeroSample small.graph site zero)
    (hit : RhsAt found rhs) : RhsAt (found.transport e) (e.vertices.address rhs) := by
  refine ⟨(e.vertices.sort_eq rhs).trans (hit.sort_eq.trans (e.vertices.sort_eq site).symm), ?_⟩
  rw [found.transport_row e]
  exact e.hasNode (r := ⟨rhs, hit.sort_eq⟩) hit.shape

theorem eligible_prefix {a b : Output P params results l} {address : Nat}
    (inclusion : Prefix a b) (eligible : EligibleAt zero a address) : EligibleAt zero b address := by
  obtain ⟨e, keep⟩ := inclusion
  obtain ⟨i, number, ⟨found⟩⟩ := eligible
  exact ⟨e.vertices.address i, (keep i).trans number, ⟨found.transport e⟩⟩

theorem complete_prefix {a b : Output P params results l} {address : Nat}
    (inclusion : Prefix a b) (done : CompleteAt zero a address) : CompleteAt zero b address := by
  obtain ⟨e, keep⟩ := inclusion
  obtain ⟨site, found, number, rhs, hit, joined⟩ := done
  exact ⟨e.vertices.address site, found.transport e, (keep site).trans number,
    e.vertices.address rhs, rhs_transport e found hit, e.classes site rhs joined⟩

private theorem reuse_streamEq (found : ZeroSample small.graph site zero)
    (hit : RhsAt found rhs) (zeroLaw : m.run zero .nil = some ⟨0⟩)
    {values : small.graph.Valuation m} (solves : small.graph.Solves m env values) :
    StreamEq values site rhs := by
  let target : Ref small.graph.sort (small.graph.sort site) := ⟨rhs, hit.sort_eq⟩
  have zeroAt (i : Index l) : Rules.readRef values found.count i = some ⟨0⟩ :=
    (Rules.at_label solves found.countNode i).trans zeroLaw
  exact (Rules.streamEq_iff_vertex (Ref.ofId small.graph.sort site) target).mp
    (Rules.eval_zero_theta solves found.evalNode found.thetaNode hit.shape zeroAt)

variable [DecidableEq Data]

theorem ensure_cert (found : ZeroSample small.graph site zero) :
    Prefix ⟨n, small⟩ (ensure found) ∧ CompleteAt zero (ensure found) site.val := by
  unfold ensure
  cases choice : choose found small.classes with
  | keep =>
    exact ⟨prefix_refl _, site, found, rfl, (keep_iff found small.classes).mp choice⟩
  | reuse i =>
    let e : Embedding small (⟨small.graph, small.classes.merge site i⟩ : State P params results n l) :=
      { Embedding.refl small with
        classes := by
          intro a b joined
          rw [Embedding.refl_address, Embedding.refl_address]
          exact Classes.merge_preserves _ _ _ joined }
    exact ⟨⟨e, fun j => congrArg Fin.val (Embedding.refl_address small j)⟩,
      site, found, rfl, i, reuse_sound found small.classes choice, Classes.merge_equates _ _ _⟩
  | append =>
    let e := found.step.embedding
    have shape : RhsAt (found.transport e) (Fin.last n) := by
      refine ⟨found.row.sort_fresh.trans (e.vertices.sort_eq site).symm, ?_⟩
      rw [found.transport_row e, Embedding.mapRow]
      change HEq (found.step.apply.graph.node (Fin.last n))
        (Node.ofLabel found.row.label (e.vertices.tuple found.row.args))
      rw [show e.vertices = found.row.vertices from found.step.embedding_vertices]
      exact found.row.node_fresh
    have eq := found.step.embedding_address site
    exact ⟨⟨e, fun j => congrArg Fin.val (found.step.embedding_address j)⟩,
      e.vertices.address site, found.transport e, congrArg Fin.val eq,
      Fin.last n, shape, eq.symm ▸ found.equates⟩

theorem ensure_preserves (found : ZeroSample small.graph site zero)
    (zeroLaw : m.run zero .nil = some ⟨0⟩) :
    Preserves m env ⟨n, small⟩ (ensure found) := by
  unfold ensure
  cases choice : choose found small.classes with
  | keep => exact fun wf valid => ⟨wf, valid, fun _ => rfl⟩
  | reuse i =>
    intro wf valid
    have hit := reuse_sound found small.classes choice
    exact ⟨wf, Classes.merge_sound valid
      (reuse_streamEq found hit zeroLaw (small.graph.denote_solves m env wf)), fun _ => rfl⟩
  | append =>
    intro wf valid
    let after := found.row.demandWellFounded wf
    exact ⟨after, found.step.sound wf valid (found.holds zeroLaw), found.row.observe_eq wf after⟩

variable [DecidableEq (P [] .count)]

theorem visit_known (s : Output P params results l) {site : Fin s.1} (found : ZeroSample s.2.graph site zero) :
    visit zero s site.val = ensure found := by
  obtain ⟨address, bound⟩ := site
  unfold visit
  rw [dite_eq_left bound, found.matchAt_of_witness]

theorem visit_prefix (s : Output P params results l) (address : Nat) : Prefix s (visit zero s address) := by
  unfold visit
  split
  · split
    · exact (ensure_cert _).1
    · exact prefix_refl _
  · exact prefix_refl _

theorem visit_complete {s : Output P params results l} {address : Nat}
    (eligible : EligibleAt zero s address) : CompleteAt zero (visit zero s address) address := by
  obtain ⟨site, rfl, ⟨found⟩⟩ := eligible
  rw [visit_known s found]
  exact (ensure_cert found).2

theorem visit_preserves (s : Output P params results l) (address : Nat)
    (zeroLaw : m.run zero .nil = some ⟨0⟩) : Preserves m env s (visit zero s address) := by
  unfold visit
  split
  · split
    · exact ensure_preserves _ zeroLaw
    · exact fun wf valid => ⟨wf, valid, fun _ => rfl⟩
  · exact fun wf valid => ⟨wf, valid, fun _ => rfl⟩

theorem check_done_iff (s : Output P params results l) (address : Nat) :
    checkDone zero s address = true ↔ CompleteAt zero s address := by
  constructor
  · intro ok
    unfold checkDone at ok
    by_cases bound : address < s.1
    · rw [dite_eq_left bound] at ok
      cases hit : ZeroSample.matchAt (g := s.2.graph) ⟨address, bound⟩ zero with
      | none => rw [hit] at ok; cases ok
      | some found =>
        rw [hit] at ok
        exact ⟨⟨address, bound⟩, found, rfl, (check_covered_iff _ _).mp ok⟩
    · rw [dite_eq_right bound] at ok
      cases ok
  · rintro ⟨site, found, rfl, covered⟩
    obtain ⟨address, bound⟩ := site
    unfold checkDone
    rw [dite_eq_left bound, found.matchAt_of_witness]
    exact (check_covered_iff _ _).mpr covered

theorem visit_done {s : Output P params results l} {address : Nat}
    (done : CompleteAt zero s address) : visit zero s address = s := by
  obtain ⟨site, found, rfl, covered⟩ := done
  rw [visit_known s found]
  unfold ensure
  rw [(keep_iff _ _).mpr covered]

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup
