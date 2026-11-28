module

public import Silmaril.Semantics.TrackA.Interaction.Relabel.Defs

public section

namespace Silmaril.Proofs.Semantics.TrackA.Interaction.Relabel

open Silmaril.Semantics.TrackA.Interaction

universe u v w x y z b d s i

variable {S : Signature.{u,v}} {T : Signature.{w,x}} {A : Type y} {B : Signature.{b,d}}
  {X : Type z} (f : Signature.TraceHom S T) (c : Coalgebra S B A X)

private theorem internal_iff {a b : X} :
    (c.relabel f.hom).Internal a b ↔ c.Internal a b := by
  constructor
  · rintro (step | ⟨kind, shape, j, step⟩)
    · cases step with
      | tau h =>
        cases layer : c a <;> simp [Coalgebra.relabel, layer, Node.relabel] at h
        exact .inl (.tau (layer.trans (congrArg Node.tau h)))
    · cases step with
      | choice h =>
        cases layer : c a <;> simp only [Coalgebra.relabel, layer, Node.relabel] at h <;> try contradiction
        obtain ⟨rfl, rfl, kont⟩ := Node.branch.inj h
        cases kont
        exact .inr ⟨_, _, j, .choice layer j⟩
  · rintro (step | ⟨kind, shape, j, step⟩)
    · cases step with
      | tau h => exact .inl (.tau (by simp [Coalgebra.relabel, h, Node.relabel]))
    · cases step
      rename_i next h
      have layer : c.relabel f.hom a = .branch kind shape next := by
        simp [Coalgebra.relabel, h, Node.relabel]
      exact .inr ⟨kind, shape, j, .choice layer j⟩

private theorem internal_eq : (c.relabel f.hom).Internal = c.Internal := by
  funext a b
  exact propext (internal_iff f c)

private theorem exchange_step_image {a b : X} {event : T.Exchange} :
    (c.relabel f.hom).Step a (.exchange event) b ↔
      ∃ source, c.Step a (.exchange source) b ∧ f.exchange source = event := by
  constructor
  · intro step
    cases step with
    | vis h r =>
      cases layer : c a <;> simp only [Coalgebra.relabel, layer, Node.relabel] at h <;> try contradiction
      case vis.vis q k =>
        obtain ⟨hq, hk⟩ := Node.vis.inj h
        cases hq
        cases hk
        exact ⟨⟨q, f.hom.response q r⟩, .vis layer _, Sigma.ext rfl
          (heq_of_eq ((f.reply q).apply_symm_apply r))⟩
  · rintro ⟨source, step, rfl⟩
    cases step with
    | @vis q k h r =>
      have layer : c.relabel f.hom a = .vis (f.hom.request q) (fun reply => k (f.hom.response q reply)) :=
        by simp [Coalgebra.relabel, h, Node.relabel]
      have decoded : f.hom.response q (f.reply q r) = r := (f.reply q).symm_apply_apply r
      simpa only [Signature.TraceHom.exchange, decoded] using Coalgebra.Step.vis layer (f.reply q r)

private theorem weak_step_image {a b : X} {event : T.Exchange} :
    (c.relabel f.hom).WeakStep a event b ↔
      ∃ source, c.WeakStep a source b ∧ f.exchange source = event := by
  simp only [Coalgebra.WeakStep, Coalgebra.Silent, internal_eq f c, exchange_step_image f c]
  constructor
  · rintro ⟨mid, reach, source, step, rfl⟩
    exact ⟨source, ⟨mid, reach, step⟩, rfl⟩
  · rintro ⟨source, ⟨mid, reach, step⟩, rfl⟩
    exact ⟨mid, reach, source, step, rfl⟩

private theorem follows_image {a b : X} {events : List T.Exchange} :
    (c.relabel f.hom).Follows a events b ↔
      ∃ source, c.Follows a source b ∧ source.map f.exchange = events := by
  constructor
  · intro follows
    induction follows with
    | nil a => exact ⟨[], .nil a, rfl⟩
    | cons first _ ih =>
      obtain ⟨event, step, rfl⟩ := (weak_step_image f c).mp first
      obtain ⟨events, rest, rfl⟩ := ih
      exact ⟨event :: events, .cons step rest, rfl⟩
  · rintro ⟨source, follows, rfl⟩
    induction follows with
    | nil a => exact .nil a
    | cons first _ ih => exact .cons ((weak_step_image f c).mpr ⟨_, first, rfl⟩) ih

private theorem ending_image {state : X} {ending : End T A} :
    (c.relabel f.hom).EndsAt state ending ↔
      ∃ source, c.EndsAt state source ∧ source.relabel f.hom = ending := by
  constructor
  · cases ending with
    | returned a =>
      intro h
      cases layer : c state <;> simp [Coalgebra.EndsAt, Coalgebra.relabel, layer, Node.relabel] at h
      exact ⟨.returned a, layer.trans (congrArg Node.ret h), rfl⟩
    | stuck q =>
      rintro ⟨empty, k, h⟩
      cases layer : c state <;> simp only [Coalgebra.relabel, layer, Node.relabel] at h <;> try contradiction
      case vis q' k' =>
        have hq := (Node.vis.inj h).1
        cases hq
        exact ⟨.stuck q', ⟨⟨fun r => empty.false (f.reply q' r)⟩, k', layer⟩, rfl⟩
    | deadlock kind =>
      rintro ⟨shape, empty, k, h⟩
      cases layer : c state <;> simp only [Coalgebra.relabel, layer, Node.relabel] at h <;> try contradiction
      case branch kind' shape' k' =>
        obtain ⟨rfl, rfl, _⟩ := Node.branch.inj h
        exact ⟨.deadlock _, ⟨shape', empty, k', layer⟩, rfl⟩
    | diverge =>
      intro h
      exact ⟨.diverge, by simpa only [Coalgebra.EndsAt, internal_eq f c] using h, rfl⟩
  · rintro ⟨source, ends, rfl⟩
    cases source with
    | returned a => simp [Coalgebra.EndsAt, End.relabel, Coalgebra.relabel, Node.relabel,
        show c state = .ret a from ends]
    | stuck q =>
      obtain ⟨empty, k, h⟩ := ends
      exact ⟨⟨fun r => empty.false (f.hom.response q r)⟩, fun r => k (f.hom.response q r),
        by simp [Coalgebra.relabel, h, Node.relabel]⟩
    | deadlock kind =>
      obtain ⟨shape, empty, k, h⟩ := ends
      exact ⟨shape, empty, k, by simp [Coalgebra.relabel, h, Node.relabel]⟩
    | diverge => simpa only [Coalgebra.EndsAt, End.relabel, internal_eq f c] using ends

theorem coalgebra_observes (state : X) :
    (c.relabel f.hom).observes state = Trace.relabel f '' (c.observes state) := by
  ext trace
  constructor
  · intro observed
    cases trace with
    | finite events ending =>
      obtain ⟨mid, last, follows, silent, ends⟩ := observed
      obtain ⟨sourceEvents, sourceFollows, mappedEvents⟩ := (follows_image f c).mp follows
      obtain ⟨sourceEnd, sourceEnds, mappedEnd⟩ := (ending_image f c).mp ends
      refine ⟨.finite sourceEvents sourceEnd, ⟨mid, last, sourceFollows, ?_, sourceEnds⟩,
        congrArg₂ Trace.finite mappedEvents mappedEnd⟩
      simpa only [Coalgebra.Silent, internal_eq f c] using silent
    | infinite events =>
      obtain ⟨path, initial, follows⟩ := observed
      choose source steps relabels using fun n => (weak_step_image f c).mp (follows n)
      exact ⟨.infinite source, ⟨path, initial, steps⟩, congrArg Trace.infinite (funext relabels)⟩
  · rintro ⟨source, observed, rfl⟩
    cases source with
    | finite events ending =>
      obtain ⟨mid, last, follows, silent, ends⟩ := observed
      refine ⟨mid, last, (follows_image f c).mpr ⟨events, follows, rfl⟩,
        ?_, (ending_image f c).mpr ⟨ending, ends, rfl⟩⟩
      simpa only [Coalgebra.Silent, internal_eq f c] using silent
    | infinite events =>
      obtain ⟨path, initial, follows⟩ := observed
      exact ⟨path, initial, fun n => (weak_step_image f c).mpr ⟨events n, follows n, rfl⟩⟩

theorem forest_observes {I : Type i} (forest : Forest.{u,v,b,d,y,i,s} S B A I) :
    (forest.relabel f.hom).observes = Trace.relabel f '' forest.observes := by
  ext trace
  constructor
  · rintro ⟨root, run⟩
    obtain ⟨source, sourceRun, mapped⟩ := (coalgebra_observes f forest.unfold (forest.root root)) ▸ run
    exact ⟨source, ⟨root, sourceRun⟩, mapped⟩
  · rintro ⟨source, ⟨root, run⟩, rfl⟩
    exact ⟨root, (coalgebra_observes f forest.unfold (forest.root root)).symm ▸ ⟨source, run, rfl⟩⟩

end Silmaril.Proofs.Semantics.TrackA.Interaction.Relabel
