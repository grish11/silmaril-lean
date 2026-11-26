module

public import Silmaril.Semantics.ITree.Trace.Silence.Defs
import Silmaril.Semantics.ITree.Trace.Thms

@[expose] public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree

open Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A B : Type v}

theorem silent_vis_iff {R S : Type u} (e : E R) (k : R → Tree E A)
    (event : E S) (reply : S) (tail : ExchangePath E) :
    SilentAfter (vis e k) (.cons event reply tail) ↔
      ∃ h : S = R, h ▸ event = e ∧ SilentAfter (k (h ▸ reply)) tail := by
  constructor
  · rintro ⟨next, equal, seen⟩
    rw [out_vis] at equal
    have root := Part.some_injective equal
    rw [Visible.vis.injEq] at root
    rcases root with ⟨rfl, eventEq, nextEq⟩
    exact ⟨rfl, (eq_of_heq eventEq).symm, (eq_of_heq nextEq) ▸ seen⟩
  · rintro ⟨rfl, rfl, seen⟩
    exact ⟨k, out_vis _ _, seen⟩

theorem silent_vis_same_iff {R : Type u} (event : E R) (k : R → Tree E A)
    (reply : R) (tail : ExchangePath E) :
    SilentAfter (vis event k) (.cons event reply tail) ↔ SilentAfter (k reply) tail := by
  rw [silent_vis_iff]
  exact ⟨fun ⟨h, _, seen⟩ => by simpa only [show h = rfl from Subsingleton.elim _ _] using seen,
    fun seen => ⟨rfl, rfl, seen⟩⟩

private theorem reply_related {R : Type u} (event : E R) {k l : R → Tree E A}
    (h : TraceLEWithSilence (vis event k) (vis event l)) (reply : R) :
    TraceLEWithSilence (k reply) (l reply) := by
  constructor
  · intro trace seen
    exact (hasTrace_vis_exchange_iff event l reply trace).mp
      (h.1 _ ((hasTrace_vis_exchange_iff event k reply trace).mpr seen))
  · intro path seen
    exact (silent_vis_same_iff event l reply path).mp
      (h.2 _ ((silent_vis_same_iff event k reply path).mpr seen))

theorem trace_with_silence_mutual {t s : Tree E A} :
    TraceLEWithSilence t s ↔ TraceLE t s ∧ TraceLE s t := by
  refine ⟨?_, fun ⟨left, right⟩ => ⟨left, left.antisymm right ▸ fun _ seen => seen⟩⟩
  intro h
  refine ⟨h.1, ?_⟩
  suffices same : t = s by exact same ▸ TraceLE.refl t
  apply Tree.eq_iff_observe.mpr
  intro depth
  induction depth generalizing t s with
  | zero => exact Subsingleton.elim _ _
  | succ depth ih =>
    rcases cases_visible t with rfl | ⟨value, rfl⟩ | ⟨R, event, k, rfl⟩
    · have quiet : out s = Part.none := h.2 .nil (out_diverge)
      rw [(out_eq_none_iff s).mp quiet]
    · have returned : out s = Part.some (.ret value) := h.1 (.result value) (out_ret value)
      rw [out_injective (returned.trans (out_ret value).symm)]
    · obtain ⟨l, seen⟩ := h.1 (.request event) (hasTrace_vis_request event k)
      have same : s = vis event l := out_injective (seen.trans (out_vis event l).symm)
      subst s
      have children : (fun r => (k r).observe depth) = fun r => (l r).observe depth :=
        funext fun reply => ih (reply_related event h reply)
      simp only [observe_succ_eq_out, out_vis, Part.map_eq_map, Part.map_some, Visible.map_vis,
        Function.comp_def, children]

theorem silent_bind_pure (f : A → B) (t : Tree E A) (path : ExchangePath E) :
    SilentAfter (t >>= fun a => pure (f a)) path ↔ SilentAfter t path := by
  induction path generalizing t with
  | nil =>
    rcases cases_visible t with rfl | ⟨value, rfl⟩ | ⟨R, e, k, rfl⟩
    · simp only [diverge_bind]
      simp [SilentAfter]
    · rw [show (ret value >>= fun a => pure (f a) : Tree E B) = ret (f value) from pure_bind _ _]
      simp [SilentAfter]
    · simp only [vis_bind]
      simp [SilentAfter]
  | cons event reply tail ih =>
    rcases cases_visible t with rfl | ⟨value, rfl⟩ | ⟨R, e, k, rfl⟩
    · simp only [diverge_bind]
      simp [SilentAfter]
    · rw [show (ret value >>= fun a => pure (f a) : Tree E B) = ret (f value) from pure_bind _ _]
      simp [SilentAfter]
    · simp only [vis_bind, silent_vis_iff]
      exact exists_congr fun _ => and_congr_right fun _ => ih _

end Silmaril.Proofs.Semantics.Elgot.ITree
