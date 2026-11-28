module

public import Silmaril.Semantics.ITree.Trace.Handled.Defs
public import Silmaril.Semantics.ITree.Trace.Thms

public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree

open Silmaril.Elgot.ITree

universe u v w

variable {E : Type u → Type u} {X : Type w} {A B : Type v}
  {step : Handler X E}

private theorem handled_vis {R : Type u} {e : E R} {k l : R → Tree E A}
    {x : X} (h : HandledTraceLE step x (vis e k) (vis e l)) {r : R} {y : X}
    (exchange : step ⟨R, e⟩ x r y) : HandledTraceLE step y (k r) (l r) :=
  fun p hp => ⟨(hasTrace_vis_exchange_iff e l r p).mp
    (h (.exchange e r p) ⟨(hasTrace_vis_exchange_iff e k r p).mpr hp.1, ⟨y, exchange, hp.2⟩⟩).1,
    hp.2⟩

private theorem handled_vis_target {R : Type u} {e : E R} {k : R → Tree E A}
    {s : Tree E A} {x : X} (h : HandledTraceLE step x (vis e k) s) :
    ∃ l, s = vis e l := by
  obtain ⟨l, hl⟩ := (h (.request e) ⟨hasTrace_vis_request e k, trivial⟩).1
  exact ⟨l, out_injective (hl.trans (out_vis _ _).symm)⟩

private theorem handled_ret_target {a : A} {s : Tree E A} {x : X}
    (h : HandledTraceLE step x (ret a) s) : s = ret a :=
  out_injective ((h (.result a) ⟨out_ret a, trivial⟩).1.trans (out_ret a).symm)

theorem handled_returnsTo {x y : X} {t s : Tree E A} {a : A}
    (h : HandledTraceLE step x t s) (reached : ReturnsTo step x t y a) :
    ReturnsTo step x s y a := by
  induction reached generalizing s with
  | ret x a =>
    rw [handled_ret_target h]
    exact .ret x a
  | exchange allowed reached ih =>
    obtain ⟨l, rfl⟩ := handled_vis_target h
    exact .exchange allowed (ih (handled_vis h allowed))

private theorem ret_bind (a : A) (f : A → Tree E B) : (ret a >>= f) = f a :=
  pure_bind a f

theorem handled_bind {x : X} {t s : Tree E A} {f g : A → Tree E B}
    (h : HandledTraceLE step x t s)
    (hk : ∀ {y a}, ReturnsTo step x t y a → HandledTraceLE step y (f a) (g a)) :
    HandledTraceLE step x (t >>= f) (s >>= g) := by
  intro trace
  induction trace generalizing x t s
  case «prefix» => exact id
  case' request => intro seen
  case' exchange R d r tail ih => intro seen
  case' result => intro seen
  all_goals
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · exact False.elim (by simpa [diverge_bind] using seen.1)
    · rw [handled_ret_target h]
      rw [ret_bind] at seen ⊢
      exact hk (.ret x a) _ seen
  all_goals
    obtain ⟨l, rfl⟩ := handled_vis_target h
    rw [vis_bind] at seen ⊢
  case request =>
    exact ⟨(hasTrace_vis_request_iff _ _ _).mpr ((hasTrace_vis_request_iff _ _ _).mp seen.1), seen.2⟩
  case exchange =>
    obtain ⟨sameType, sameEvent, htail⟩ := (hasTrace_vis_exchange _ _ _ _ _).mp seen.1
    cases sameType
    cases sameEvent
    obtain ⟨y, exchange, replay⟩ := seen.2
    have next := ih (handled_vis h exchange) (fun reached => hk (.exchange exchange reached))
      ⟨htail, replay⟩
    exact ⟨(hasTrace_vis_exchange_iff _ _ r tail).mpr next.1, ⟨y, exchange, next.2⟩⟩
  case result =>
    have impossible := seen.1
    simp [HasTrace, out_vis] at impossible

end Silmaril.Proofs.Semantics.Elgot.ITree
