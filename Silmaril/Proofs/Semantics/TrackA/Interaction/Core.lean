module

public import Silmaril.Semantics.TrackA.Interaction.Defs

public section

namespace Silmaril.Proofs.Semantics.TrackA.Interaction

open Silmaril.Semantics.TrackA.Interaction

universe u v w x y z

variable {S : Signature.{u,v}} {B : Signature.{w,x}} {A : Type y} {X : Type z}

namespace Coalgebra

variable {c : Coalgebra S B A X} {start next : X}

private theorem internal_of_tau (h : c start = .tau next) :
    ∀ {target}, c.Internal start target → target = next := by
  intro target step
  rcases step with step | ⟨_, _, _, step⟩
  · cases step with
    | tau edge => exact Node.tau.inj (edge.symm.trans h)
  · cases step with
    | choice edge _ => cases edge.symm.trans h

private theorem no_exchange_of_tau (h : c start = .tau next) {e : S.Exchange} {target : X} :
    ¬ c.Step start (.exchange e) target := by
  intro step
  cases step with
  | vis edge _ => cases edge.symm.trans h

private theorem weakStep_of_tau (h : c start = .tau next) {e : S.Exchange} {target : X} :
    c.WeakStep start e target → c.WeakStep next e target := by
  rintro ⟨middle, silent, exchange⟩
  rcases silent.cases_head with rfl | ⟨state, first, rest⟩
  · exact (no_exchange_of_tau h exchange).elim
  · obtain rfl := internal_of_tau h first
    exact ⟨middle, rest, exchange⟩

private theorem endsAt_of_tau (h : c start = .tau next) {ending : End S A}
    (ends : c.EndsAt start ending) : c.EndsAt next ending := by
  cases ending with
  | returned a => cases (show c start = .ret a from ends).symm.trans h
  | stuck q =>
    obtain ⟨_, k, edge⟩ := ends
    cases edge.symm.trans h
  | deadlock kind =>
    obtain ⟨_, _, _, edge⟩ := ends
    cases edge.symm.trans h
  | diverge =>
    obtain ⟨_, first, rest⟩ := InfiniteTrace.unfold ends
    exact internal_of_tau h first ▸ rest

private theorem finite_of_tau (h : c start = .tau next) {es : List S.Exchange} {ending : End S A} :
    Trace.finite es ending ∈ c.observes start → Trace.finite es ending ∈ c.observes next := by
  rintro ⟨middle, last, withHead, silent, ends⟩
  cases withHead with
  | nil =>
    rcases silent.cases_head with rfl | ⟨_, first, rest⟩
    · exact ⟨next, next, .nil _, .refl, endsAt_of_tau h ends⟩
    · exact ⟨next, last, .nil _, internal_of_tau h first ▸ rest, ends⟩
  | cons first rest =>
    exact ⟨middle, last, .cons (weakStep_of_tau h first) rest, silent, ends⟩

private theorem runsInfinite_of_tau (h : c start = .tau next) {es : Nat → S.Exchange} :
    c.RunsInfinite start es → c.RunsInfinite next es := by
  rintro ⟨path, first, follows⟩
  refine ⟨fun n => match n with | 0 => next | i + 1 => path (i + 1), rfl, ?_⟩
  intro n
  cases n with
  | zero => exact weakStep_of_tau h (first ▸ follows 0)
  | succ n => exact follows (n + 1)

theorem observes_mono_internal (edge : c.Internal start next) :
    c.observes next ⊆ c.observes start := by
  have withHead {e : S.Exchange} {y : X} :
      c.WeakStep next e y → c.WeakStep start e y := by
    rintro ⟨middle, silent, exchange⟩
    exact ⟨middle, silent.head edge, exchange⟩
  intro trace accepts
  cases trace with
  | finite es ending =>
    obtain ⟨middle, last, follows, silent, ends⟩ := accepts
    cases follows with
    | nil => exact ⟨start, last, .nil _, silent.head edge, ends⟩
    | cons first rest => exact ⟨middle, last, .cons (withHead first) rest, silent, ends⟩
  | infinite es =>
    obtain ⟨path, first, follows⟩ := accepts
    refine ⟨fun n => match n with | 0 => start | i + 1 => path (i + 1), rfl, ?_⟩
    intro n
    cases n with
    | zero => exact withHead (first ▸ follows 0)
    | succ n => exact follows (n + 1)

theorem observes_tau (h : c start = .tau next) : c.observes start = c.observes next := by
  apply Set.Subset.antisymm _ (observes_mono_internal (.inl (.tau h)))
  intro trace accepts
  cases trace with
  | finite => exact finite_of_tau h accepts
  | infinite => exact runsInfinite_of_tau h accepts

theorem observes_silent_loop (h : c start = .tau start) :
    Trace.finite [] .diverge ∈ c.observes start := by
  refine ⟨start, start, .nil _, .refl, ?_⟩
  exact ⟨fun _ => start, rfl, fun _ => .inl (.tau h)⟩

theorem observes_visible_loop {q : S.Request} (reply : S.Response q)
    (h : c start = .vis q (fun _ => start)) :
    Trace.infinite (fun _ => ⟨q, reply⟩) ∈ c.observes start :=
  ⟨fun _ => start, rfl, fun _ => ⟨start, .refl, .vis h reply⟩⟩

end Coalgebra
end Silmaril.Proofs.Semantics.TrackA.Interaction
