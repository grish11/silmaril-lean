module

public import Silmaril.Semantics.ITree.Trace.Defs
public import Silmaril.Semantics.ITree.Thms
import Silmaril.Semantics.Elgot.Thms

public section

namespace Silmaril.Proofs.Semantics.Elgot.ITree

open Silmaril.Elgot.ITree

universe u v

variable {E : Type u → Type u} {A B : Type v}

theorem trace_exchange_vis_iff {R S : Type u} (e : E R) (k : R → Tree E A)
    (d : E S) (r : S) (tail : Trace E A) :
    HasTrace (vis e k) (.exchange d r tail) ↔
      ∃ h : S = R, h ▸ d = e ∧ HasTrace (k (h ▸ r)) tail := by
  constructor
  · rintro ⟨next, heq, htail⟩
    rw [out_vis] at heq
    have heq := Part.some_injective heq
    rw [Visible.vis.injEq] at heq
    rcases heq with ⟨rfl, he, hk⟩
    exact ⟨rfl, (eq_of_heq he).symm, (eq_of_heq hk) ▸ htail⟩
  · rintro ⟨rfl, rfl, h⟩
    exact ⟨k, out_vis _ _, h⟩

theorem trace_request_vis_iff {R S : Type u} (e : E R) (k : R → Tree E A) (d : E S) :
    HasTrace (vis e k) (.request d) ↔ ∃ h : S = R, h ▸ d = e := by
  constructor
  · rintro ⟨next, heq⟩
    rw [out_vis] at heq
    have heq := Part.some_injective heq
    rw [Visible.vis.injEq] at heq
    rcases heq with ⟨rfl, he, _⟩
    exact ⟨rfl, (eq_of_heq he).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨k, out_vis _ _⟩

theorem trace_vis_mono {R : Type u} (e : E R) {k l : R → Tree E A}
    (h : ∀ r, TraceLE (k r) (l r)) : TraceLE (vis e k) (vis e l) := by
  intro p
  cases p with
  | «prefix» => exact fun _ => trivial
  | request d => simp only [trace_request_vis_iff, imp_self]
  | exchange d r tail =>
    simp only [trace_exchange_vis_iff]
    rintro ⟨hr, he, hp⟩
    exact ⟨hr, he, h _ _ hp⟩
  | result a => simp [HasTrace]

theorem trace_diverge_iff (p : Trace E A) :
    HasTrace (diverge : Tree E A) p ↔ p = .prefix := by
  cases p <;> simp [HasTrace, out_diverge]

private theorem ret_bind_tree (a : A) (f : A → Tree E B) :
    (ret a >>= f) = f a :=
  pure_bind a f

theorem trace_bind_right_mono (t : Tree E A) {f g : A → Tree E B}
    (h : ∀ a, TraceLE (f a) (g a)) : TraceLE (t >>= f) (t >>= g) := by
  intro p
  induction p generalizing t with
  | «prefix» => exact fun _ => trivial
  | request d =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · simp only [diverge_bind]
      exact id
    · simpa only [ret_bind_tree] using h a (.request d)
    · simpa only [vis_bind, trace_request_vis_iff] using id
  | exchange d r tail ih =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · simp only [diverge_bind]
      exact id
    · simpa only [ret_bind_tree] using
        h a (.exchange d r tail)
    · simp only [vis_bind, trace_exchange_vis_iff]
      rintro ⟨hr, he, hp⟩
      exact ⟨hr, he, ih _ hp⟩
  | result b =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · simp only [diverge_bind]
      exact id
    · simpa only [ret_bind_tree] using h a (.result b)
    · simp [vis_bind, HasTrace, out_vis]

private theorem trace_map_forward (f : A → B) (t : Tree E A) (p : Trace E A)
    (h : HasTrace t p) : HasTrace (t >>= fun a => pure (f a)) (p.map f) := by
  induction p generalizing t with
  | «prefix» => trivial
  | request d =>
    obtain ⟨k, hk⟩ := h
    have ht : t = vis d k := out_injective (hk.trans (out_vis _ _).symm)
    rw [ht, vis_bind]
    exact ⟨_, out_vis _ _⟩
  | exchange d r tail ih =>
    obtain ⟨k, hk, htail⟩ := h
    have ht : t = vis d k := out_injective (hk.trans (out_vis _ _).symm)
    rw [ht, vis_bind]
    exact ⟨_, out_vis _ _, ih _ htail⟩
  | result a =>
    have ht : t = ret a := out_injective (h.trans (out_ret _).symm)
    rw [ht, ret_bind_tree]
    exact out_ret (f a)

private theorem trace_map_backward (f : A → B) (t : Tree E A) (p : Trace E B)
    (h : HasTrace (t >>= fun a => pure (f a)) p) :
    ∃ q, HasTrace t q ∧ q.map f = p := by
  induction p generalizing t with
  | «prefix» => exact ⟨.prefix, trivial, rfl⟩
  | request d =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [diverge_bind] at h
      simp [trace_diverge_iff] at h
    · rw [ret_bind_tree] at h
      change HasTrace (ret (f a)) _ at h
      simp [HasTrace] at h
    · rw [vis_bind, trace_request_vis_iff] at h
      exact ⟨.request d, (trace_request_vis_iff e k d).mpr h, rfl⟩
  | exchange d r tail ih =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [diverge_bind] at h
      simp [trace_diverge_iff] at h
    · rw [ret_bind_tree] at h
      change HasTrace (ret (f a)) _ at h
      simp [HasTrace] at h
    · rw [vis_bind, trace_exchange_vis_iff] at h
      obtain ⟨hr, he, ht⟩ := h
      obtain ⟨pre, hpre, hmap⟩ := ih _ ht
      exact ⟨.exchange d r pre, (trace_exchange_vis_iff e k d r pre).mpr ⟨hr, he, hpre⟩,
        congrArg (Trace.exchange d r) hmap⟩
  | result b =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [diverge_bind] at h
      simp [trace_diverge_iff] at h
    · rw [ret_bind_tree] at h
      change HasTrace (ret (f a)) _ at h
      have hval : f a = b := by simpa [HasTrace] using h
      exact ⟨.result a, out_ret a, congrArg Trace.result hval⟩
    · rw [vis_bind] at h
      simp [HasTrace] at h

theorem trace_same_exchange_iff {R : Type u} (e : E R) (k : R → Tree E A)
    (r : R) (p : Trace E A) :
    HasTrace (vis e k) (.exchange e r p) ↔ HasTrace (k r) p := by
  rw [trace_exchange_vis_iff]
  exact ⟨fun ⟨h, _, hp⟩ => by simpa only [show h = rfl from Subsingleton.elim _ _] using hp,
    fun hp => ⟨rfl, rfl, hp⟩⟩

private theorem trace_ret_right {a : A} {s : Tree E A}
    (h : TraceLE (ret a) s) : s = ret a :=
  out_injective ((h (.result a) (out_ret a)).trans (out_ret a).symm)

private theorem trace_vis_reply {R : Type u} {e : E R} {k l : R → Tree E A}
    (h : TraceLE (vis e k) (vis e l)) (r : R) : TraceLE (k r) (l r) :=
  fun p hp => (trace_same_exchange_iff e l r p).mp
    (h (.exchange e r p) ((trace_same_exchange_iff e k r p).mpr hp))

private theorem trace_vis_right {R : Type u} {e : E R} {k : R → Tree E A} {s : Tree E A}
    (h : TraceLE (vis e k) s) :
    ∃ l, s = vis e l ∧ ∀ r, TraceLE (k r) (l r) := by
  obtain ⟨l, hl⟩ := h (.request e) ⟨k, out_vis e k⟩
  have hs : s = vis e l := out_injective (hl.trans (out_vis e l).symm)
  subst s
  exact ⟨l, rfl, trace_vis_reply h⟩

theorem trace_bind_left_mono {t s : Tree E A}
    (h : TraceLE t s) (f : A → Tree E B) : TraceLE (t >>= f) (s >>= f) := by
  intro p
  induction p generalizing t s
  case «prefix» => exact fun _ => trivial
  case' request => intro hp
  case' exchange R d r tail ih => intro hp
  case' result => intro hp
  all_goals
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rw [diverge_bind] at hp
      rw [(trace_diverge_iff _).mp hp]
      trivial
    · rwa [trace_ret_right h]
    · obtain ⟨l, rfl, hkl⟩ := trace_vis_right h
      rw [vis_bind] at hp ⊢
      first
      | exact (trace_request_vis_iff _ _ _).mpr ((trace_request_vis_iff _ _ _).mp hp)
      | obtain ⟨hr, he, htail⟩ := (trace_exchange_vis_iff _ _ _ _ _).mp hp
        exact (trace_exchange_vis_iff _ _ _ _ _).mpr ⟨hr, he, ih (hkl _) htail⟩
      | simp [HasTrace] at hp

theorem trace_antisymm {t s : Tree E A} (hts : TraceLE t s) (hst : TraceLE s t) :
    t = s := by
  apply Tree.eq_iff_observe.mpr
  intro depth
  induction depth generalizing t s with
  | zero => exact Subsingleton.elim _ _
  | succ depth ih =>
    rcases cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
    · rcases cases_visible s with rfl | ⟨a, rfl⟩ | ⟨R, e, l, rfl⟩
      · rfl
      · have h := hst (.result a) (out_ret a)
        simp [trace_diverge_iff] at h
      · have h := hst (.request e) ⟨l, out_vis e l⟩
        simp [trace_diverge_iff] at h
    · rw [trace_ret_right hts]
    · obtain ⟨l, rfl, hkl⟩ := trace_vis_right hts
      have children : (fun r => (k r).observe depth) = (fun r => (l r).observe depth) :=
        funext fun r => ih (hkl r) (trace_vis_reply hst r)
      simp only [observe_succ_eq_out, out_vis, Part.map_eq_map, Part.map_some, Visible.map_vis,
        Function.comp_def, children]

theorem trace_map_iff (f : A → B) (t : Tree E A) (p : Trace E B) :
    HasTrace (t >>= fun a => pure (f a)) p ↔
      ∃ q, HasTrace t q ∧ q.map f = p :=
  ⟨trace_map_backward f t p, fun ⟨q, hq, hmap⟩ => hmap ▸ trace_map_forward f t q hq⟩

private theorem trace_map_injective {f : A → B} (injective : Function.Injective f) :
    Function.Injective (Trace.map (E := E) f) := by
  intro left right same
  induction left generalizing right with
  | «prefix» => cases right <;> simp_all [Trace.map]
  | request event => cases right <;> simp_all [Trace.map]
  | result value => cases right <;> simp_all [Trace.map, injective.eq_iff]
  | exchange event reply tail ih =>
    cases right with
    | «prefix» | request _ | result _ => simp [Trace.map] at same
    | exchange other response suffix =>
      simp only [Trace.map, Trace.exchange.injEq] at same
      obtain ⟨rfl, eventEq, replyEq, tailEq⟩ := same
      rw [eq_of_heq eventEq, eq_of_heq replyEq, ih tailEq]

theorem trace_bind_pure_map_iff {f : A → B} (injective : Function.Injective f) (tree : Tree E A)
    (trace : Trace E A) :
    HasTrace (tree >>= fun x => pure (f x)) (trace.map f) ↔ HasTrace tree trace := by
  rw [trace_map_iff]
  exact ⟨fun ⟨pre, observed, same⟩ => trace_map_injective injective same ▸ observed,
    fun observed => ⟨trace, observed, rfl⟩⟩

theorem trace_bind_pure_reflect {f : A → B} (hf : Function.Injective f)
    {t s : Tree E A} (h : TraceLE (t >>= fun a => pure (f a)) (s >>= fun a => pure (f a))) :
    TraceLE t s := by
  classical
  let decode (b : B) : Tree E A := if h : ∃ a, f a = b then pure h.choose else diverge
  have retract (a : A) : decode (f a) = pure a := by
    unfold decode
    have hex : ∃ x, f x = f a := ⟨a, rfl⟩
    rw [dite_eq_left hex, hf hex.choose_spec]
  simpa only [bind_assoc, pure_bind, retract, bind_pure] using trace_bind_left_mono h decode

theorem out_resume_runs_iff (f : A → Tree E (B ⊕ A)) (t : Tree E (B ⊕ A))
    (node : Visible E B (Tree E B)) :
    out (resume f t) = Part.some node ↔ Elgot.Part.Runs (normalizeStep f) t node := by
  rw [out_resume, Part.eq_some_iff, Elgot.Part.mem_iter_iff]

/-- The first visible layers have the same indexed request or return, with
the input bodies related before resuming their reply continuations. -/
private inductive ResumeRootMatch (f g : A → Tree E (B ⊕ A)) :
    Visible E B (Tree E B) → Visible E B (Tree E B) → Prop where
  | ret (b : B) : ResumeRootMatch f g (.ret b) (.ret b)
  | vis {R : Type u} (e : E R) {k l : R → Tree E (B ⊕ A)}
      (h : ∀ r, TraceLE (k r) (l r)) :
      ResumeRootMatch f g (.vis e (fun r => resume f (k r))) (.vis e (fun r => resume g (l r)))

private theorem normalize_repeat {f : A → Tree E (B ⊕ A)} {t t' : Tree E (B ⊕ A)}
    (h : Sum.inr t' ∈ normalizeStep f t) :
    ∃ a, t = ret (.inr a) ∧ f a = t' := by
  rcases cases_visible t with rfl | ⟨b | a, rfl⟩ | ⟨R, e, k, rfl⟩
  · simp [normalizeStep, Part.bind_eq_bind] at h
  · simp [normalizeStep, Part.bind_eq_bind] at h
  · have ht : t' = f a := by simpa [normalizeStep, Part.bind_eq_bind] using h
    exact ⟨a, rfl, ht.symm⟩
  · simp [normalizeStep, Part.bind_eq_bind] at h

private theorem normalize_runs_mono {f g : A → Tree E (B ⊕ A)}
    (hfg : ∀ a, TraceLE (f a) (g a)) {t s : Tree E (B ⊕ A)}
    (hts : TraceLE t s) {node : Visible E B (Tree E B)}
    (run : Elgot.Part.Runs (normalizeStep f) t node) :
    ∃ other, Elgot.Part.Runs (normalizeStep g) s other ∧ ResumeRootMatch f g node other := by
  induction run generalizing s with
  | @done t node h =>
    rcases cases_visible t with rfl | ⟨b | a, rfl⟩ | ⟨R, e, k, rfl⟩
    · simp [normalizeStep, Part.bind_eq_bind] at h
    · have eq : node = .ret b := by simpa [normalizeStep, Part.bind_eq_bind] using h
      subst node
      rw [trace_ret_right hts]
      exact ⟨_, .done (by simp [normalizeStep, Part.bind_eq_bind]), .ret b⟩
    · simp [normalizeStep, Part.bind_eq_bind] at h
    · have eq : node = .vis e (fun r => resume f (k r)) := by
        simpa [normalizeStep, Part.bind_eq_bind] using h
      subst node
      obtain ⟨l, rfl, hkl⟩ := trace_vis_right hts
      exact ⟨_, .done (by simp [normalizeStep, Part.bind_eq_bind]), .vis e hkl⟩
  | more h _ ih =>
    obtain ⟨a, rfl, rfl⟩ := normalize_repeat h
    rw [trace_ret_right hts]
    obtain ⟨other, hrun, hm⟩ := ih (hfg a)
    exact ⟨other, .more (by simp [normalizeStep, Part.bind_eq_bind]) hrun, hm⟩

theorem trace_resume_mono {f g : A → Tree E (B ⊕ A)} {t s : Tree E (B ⊕ A)}
    (hfg : ∀ a, TraceLE (f a) (g a)) (hts : TraceLE t s) :
    TraceLE (resume f t) (resume g s) := by
  have transfer {t s : Tree E (B ⊕ A)} (h : TraceLE t s) {node : Visible E B (Tree E B)}
      (root : out (resume f t) = Part.some node) :
      ∃ other, out (resume g s) = Part.some other ∧ ResumeRootMatch f g node other := by
    rw [out_resume_runs_iff] at root
    obtain ⟨other, run, hm⟩ := normalize_runs_mono hfg h root
    exact ⟨other, (out_resume_runs_iff _ _ _).mpr run, hm⟩
  intro p
  induction p generalizing t s with
  | «prefix» => exact fun _ => trivial
  | request e =>
    rintro ⟨k, hk⟩
    obtain ⟨_, hl, hm⟩ := transfer hts hk
    cases hm with
    | vis _ hkl => exact ⟨_, hl⟩
  | exchange e r tail ih =>
    rintro ⟨k, hk, htail⟩
    obtain ⟨_, hl, hm⟩ := transfer hts hk
    cases hm with
    | vis _ hkl => exact ⟨_, hl, ih (hkl r) htail⟩
  | result b =>
    intro hp
    obtain ⟨_, hr, hm⟩ := transfer hts hp
    cases hm with
    | ret _ => exact hr

end Silmaril.Proofs.Semantics.Elgot.ITree
