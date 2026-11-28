module

public import Silmaril.Semantics.ITree.Signature.Execution.Thms
public import Silmaril.Semantics.ITree.Trace.Thms

public section

namespace Silmaril.Elgot.ITree.Signature.Proofs

open CategoryTheory

universe u v

variable {S T : Signature.{u}} {A : Type v}

theorem out_source (f : S ⟶ T) (t : Tree S.Event A)
    (node : Visible T.Event A (Tree T.Event A)) (h : out (f.tree id t) = Part.some node) :
    ∃ source, out t = Part.some source ∧ f.visible id (f.tree id) source = node := by
  rw [f.out_tree, Part.eq_some_iff, Part.mem_map_iff] at h
  obtain ⟨source, seen, equal⟩ := h
  exact ⟨source, Part.eq_some_iff.mpr seen, equal⟩

theorem traceLE_map (f : S ⟶ T) {l r : Tree S.Event A} (included : TraceLE l r) :
    TraceLE (f.tree id l) (f.tree id r) := by
  intro trace
  induction trace generalizing l r with
  | «prefix» => exact fun _ => trivial
  | result a =>
    intro seen
    obtain ⟨node, original, equal⟩ := out_source f l (.ret a) seen
    cases node with
    | vis => cases equal
    | ret b =>
      cases equal
      rw [HasTrace, f.out_tree, included (.result b) original, Part.map_some]
      rfl
  | request event =>
    rintro ⟨next, seen⟩
    obtain ⟨node, original, equal⟩ := out_source f l (.vis event next) seen
    cases node with
    | ret => cases equal
    | @vis R source sourceNext =>
      obtain ⟨targetNext, target⟩ := included (.request source) ⟨sourceNext, original⟩
      cases equal
      refine ⟨fun reply => f.tree id (targetNext (f.reply ⟨R, source⟩ reply)), ?_⟩
      rw [f.out_tree, target, Part.map_some]
      rfl
  | exchange event reply tail ih =>
    rintro ⟨next, seen, rest⟩
    obtain ⟨node, original, equal⟩ := out_source f l (.vis event next) seen
    cases node with
    | ret => cases equal
    | @vis R source sourceNext =>
      obtain ⟨targetNext, target⟩ := included (.request source) ⟨sourceNext, original⟩
      cases equal
      let q : Request S.Event := ⟨R, source⟩
      let reply₀ := f.reply q reply
      have continuations : TraceLE (sourceNext reply₀) (targetNext reply₀) := by
        intro p hp
        obtain ⟨k, hk, found⟩ := included (.exchange source reply₀ p) ⟨sourceNext, original, hp⟩
        have same := Part.some_injective (target.symm.trans hk)
        cases same
        exact found
      refine ⟨fun x => f.tree id (targetNext (f.reply q x)), ?_, ih continuations rest⟩
      rw [f.out_tree, target, Part.map_some]
      rfl

private theorem matchRequest (f : S ⟶ T) (keys : Function.Injective f.request)
    {R : Type u} (event : S.Event R) (t : Tree S.Event A)
    (seen : HasTrace (f.tree id t) (.request (f.request ⟨R, event⟩).2)) :
    ∃ k, out t = Part.some (.vis event k) := by
  obtain ⟨next, shown⟩ := seen
  obtain ⟨node, original, equal⟩ := out_source f t _ shown
  cases node with
  | ret => cases equal
  | @vis R' event' k =>
    have same := keys (Option.some.inj (congrArg (fun
      | .ret _ => none
      | .vis e _ => some (⟨_, e⟩ : Request T.Event)) equal))
    cases same
    exact ⟨k, original⟩

theorem traceLE_reflect (f : S ⟶ T) (keys : Function.Injective f.request)
    (replies : ∀ q, Function.Surjective (f.reply q)) {l r : Tree S.Event A}
    (included : TraceLE (f.tree id l) (f.tree id r)) : TraceLE l r := by
  intro trace
  induction trace generalizing l r with
  | «prefix» => exact fun _ => trivial
  | result a =>
    intro original
    have seen : HasTrace (f.tree id l) (.result a) := by
      rw [HasTrace, f.out_tree, original, Part.map_some]
      rfl
    obtain ⟨node, found, equal⟩ := out_source f r (.ret a) (included _ seen)
    cases node <;> cases equal
    exact found
  | @request R event =>
    rintro ⟨k, seen⟩
    apply matchRequest f keys event r
    apply included
    refine ⟨fun reply => f.tree id (k (f.reply ⟨R, event⟩ reply)), ?_⟩
    rw [f.out_tree, seen, Part.map_some]
    rfl
  | @exchange R event reply tail ih =>
    rintro ⟨k, seen, rest⟩
    let q : Request S.Event := ⟨R, event⟩
    have leftHead : l = vis event k := out_injective (seen.trans (out_vis _ _).symm)
    have pending : HasTrace (f.tree id l) (.request (f.request q).2) := by
      rw [leftHead, f.tree_vis]
      exact hasTrace_vis_request _ _
    obtain ⟨next, found⟩ := matchRequest f keys event r (included _ pending)
    have rightHead : r = vis event next := out_injective (found.trans (out_vis _ _).symm)
    obtain ⟨reply', equal⟩ := replies q reply
    have continuations : TraceLE (f.tree id (k reply)) (f.tree id (next reply)) := by
      rw [leftHead, rightHead, f.tree_vis, f.tree_vis] at included
      intro p hp
      rw [← equal] at hp ⊢
      exact (hasTrace_vis_exchange_iff _ _ reply' p).mp
        (included _ ((hasTrace_vis_exchange_iff _ _ reply' p).mpr hp))
    exact ⟨next, found, ih continuations rest⟩

end Silmaril.Elgot.ITree.Signature.Proofs
