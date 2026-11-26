module

public import Silmaril.Semantics.SQLite.Isolation.Api.Defs
public import Silmaril.Semantics.ITree.Trace.Handled.Thms

public section

namespace Silmaril.Proofs.Semantics.SQLite.Isolation.Api

open Silmaril.Elgot
open Silmaril.SQLite.Isolation.Api

theorem treeSafe_ret {A : Type} (profile : AuthorityProfile) (a : A) :
    TreeSafe profile (ITree.ret a) := by
  intro p hp
  cases p with
  | «prefix» => trivial
  | result _ => trivial
  | request e =>
    rcases hp with ⟨k, hk⟩
    rw [ITree.out_ret] at hk
    cases Part.some_inj.mp hk
  | exchange e r tail =>
    rcases hp with ⟨k, hk, _⟩
    rw [ITree.out_ret] at hk
    cases Part.some_inj.mp hk

theorem treeSafe_diverge {A : Type} (profile : AuthorityProfile) :
    TreeSafe profile (ITree.diverge : ApiTree A) := by
  intro p hp
  rw [(ITree.hasTrace_diverge_iff p).mp hp]
  trivial

theorem treeSafe_vis {R A : Type} {profile : AuthorityProfile}
    {e : ApiEvent R} {k : R → ApiTree A}
    (he : EventAllowed profile ⟨R, e⟩)
    (hk : ∀ r, TreeSafe profile (k r)) :
    TreeSafe profile (ITree.vis e k) := by
  intro p hp
  cases p with
  | «prefix» => trivial
  | result _ =>
    rw [ITree.HasTrace, ITree.out_vis] at hp
    cases Part.some_inj.mp hp
  | request d =>
    obtain ⟨rfl, rfl⟩ := (ITree.hasTrace_vis_request_iff e k d).mp hp
    exact he
  | exchange d r tail =>
    obtain ⟨rfl, rfl, htail⟩ := (ITree.hasTrace_vis_exchange e k d r tail).mp hp
    exact ⟨he, hk r tail htail⟩

theorem treeSafe_guardedCall {R : Type} (profile : AuthorityProfile)
    (e : ApiEvent (Except ApiError R)) :
    TreeSafe profile (guardedCall profile e) := by
  unfold guardedCall
  cases h : checkEvent profile e with
  | ok u =>
    cases u
    exact treeSafe_vis h (fun r => treeSafe_ret profile r)
  | error reason =>
    exact treeSafe_ret profile (Except.error (ApiError.denied reason))

private theorem ret_bind {A B : Type} (a : A) (k : A → ApiTree B) :
    (ITree.ret a >>= k) = k a :=
  pure_bind a k

theorem treeSafe_bind {A B : Type} {profile : AuthorityProfile}
    {t : ApiTree A} {k : A → ApiTree B}
    (ht : TreeSafe profile t)
    (hk : ∀ a, TreeSafe profile (k a)) :
    TreeSafe profile (t >>= k) := by
  intro p
  induction p generalizing t with
  | «prefix» =>
    intro _
    trivial
  | result b =>
    intro _
    trivial
  | request d =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, next, rfl⟩
    · simp [ITree.diverge_bind] at hp
    · rw [ret_bind] at hp
      exact hk a (.request d) hp
    · rw [ITree.vis_bind] at hp
      obtain ⟨hR, he⟩ := (ITree.hasTrace_vis_request_iff e _ d).mp hp
      cases hR
      cases he
      exact ht (.request d) (ITree.hasTrace_vis_request d next)
  | exchange d r tail ih =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, next, rfl⟩
    · simp [ITree.diverge_bind] at hp
    · rw [ret_bind] at hp
      exact hk a (.exchange d r tail) hp
    · rw [ITree.vis_bind] at hp
      obtain ⟨hR, he, htail⟩ := (ITree.hasTrace_vis_exchange e _ d r tail).mp hp
      cases hR
      cases he
      refine ⟨ht (.request d) (ITree.hasTrace_vis_request d next), ?_⟩
      have hnext : TreeSafe profile (next r) := fun q hq =>
        (ht (.exchange d r q) ((ITree.hasTrace_vis_exchange_iff d next r q).mpr hq)).2
      exact ih hnext htail

theorem handledTreeSafe_vis {S R A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {e : ApiEvent R} {k : R → ApiTree A}
    (he : EventAllowed profile ⟨R, e⟩)
    (hk : ∀ r s', step ⟨R, e⟩ s r s' → HandledTreeSafe profile step s' (k r)) :
    HandledTreeSafe profile step s (ITree.vis e k) := by
  intro p hp
  cases p with
  | «prefix» => trivial
  | result _ =>
    have h1 := hp.1
    rw [ITree.HasTrace, ITree.out_vis] at h1
    cases Part.some_inj.mp h1
  | request d =>
    obtain ⟨rfl, rfl⟩ := (ITree.hasTrace_vis_request_iff e k d).mp hp.1
    exact he
  | exchange d r tail =>
    obtain ⟨rfl, rfl, htail⟩ := (ITree.hasTrace_vis_exchange e k d r tail).mp hp.1
    rcases hp.2 with ⟨s', hstep, hrep⟩
    exact ⟨he, hk r s' hstep tail ⟨htail, hrep⟩⟩

theorem handledTreeSafe_bind {S A B : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {s : S} {t : ApiTree A} {k : A → ApiTree B}
    (ht : HandledTreeSafe profile step s t)
    (hk : ∀ y a, ITree.ReturnsTo step s t y a → HandledTreeSafe profile step y (k a)) :
    HandledTreeSafe profile step s (t >>= k) := by
  intro p
  induction p generalizing s t with
  | «prefix» =>
    intro _
    trivial
  | result _ =>
    intro _
    trivial
  | request d =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, next, rfl⟩
    · exact False.elim (by simpa [ITree.diverge_bind, ITree.hasTrace_diverge_iff] using hp.1)
    · rw [ret_bind] at hp
      exact hk s a (.ret s a) (.request d) hp
    · rw [ITree.vis_bind] at hp
      obtain ⟨hR, he⟩ := (ITree.hasTrace_vis_request_iff e _ d).mp hp.1
      cases hR
      cases he
      exact ht (.request d) ⟨ITree.hasTrace_vis_request d next, trivial⟩
  | exchange d r tail ih =>
    intro hp
    rcases ITree.cases_visible t with rfl | ⟨a, rfl⟩ | ⟨R, e, next, rfl⟩
    · exact False.elim (by simpa [ITree.diverge_bind, ITree.hasTrace_diverge_iff] using hp.1)
    · rw [ret_bind] at hp
      exact hk s a (.ret s a) (.exchange d r tail) hp
    · rw [ITree.vis_bind] at hp
      obtain ⟨hR, he, htail⟩ := (ITree.hasTrace_vis_exchange e _ d r tail).mp hp.1
      cases hR
      cases he
      rcases hp.2 with ⟨mid, hstep, hrep⟩
      refine ⟨ht (.request d) ⟨ITree.hasTrace_vis_request d next, trivial⟩, ?_⟩
      have hnext : HandledTreeSafe profile step mid (next r) := fun q hq =>
        (ht (.exchange d r q)
          ⟨(ITree.hasTrace_vis_exchange_iff d next r q).mpr hq.1, ⟨mid, hstep, hq.2⟩⟩).2
      exact ih hnext (fun y a hret => hk y a (.exchange hstep hret)) ⟨htail, hrep⟩

theorem replayTo_iff_replay {S A : Type} (step : ApiHandler S) (s : S) (p : ApiTrace A) :
    (∃ s', ReplayTo step s p s') ↔ ITree.Replay step s p := by
  induction p generalizing s with
  | «prefix» =>
    exact ⟨fun _ => trivial, fun _ => ⟨s, rfl⟩⟩
  | request _ =>
    exact ⟨fun _ => trivial, fun _ => ⟨s, rfl⟩⟩
  | result _ =>
    exact ⟨fun _ => trivial, fun _ => ⟨s, rfl⟩⟩
  | exchange e r tail ih =>
    constructor
    · rintro ⟨s', mid, hstep, htail⟩
      exact ⟨mid, hstep, (ih mid).mp ⟨s', htail⟩⟩
    · rintro ⟨mid, hstep, hrep⟩
      obtain ⟨s', htail⟩ := (ih mid).mpr hrep
      exact ⟨s', mid, hstep, htail⟩

theorem replayTo_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {p : ApiTrace A}
    (hsafe : TraceSafe profile p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s := by
  induction p generalizing s with
  | «prefix» => cases hrep; rfl
  | request _ => cases hrep; rfl
  | result _ => cases hrep; rfl
  | exchange e r tail ih =>
    rcases hsafe with ⟨he, htailSafe⟩
    rcases hrep with ⟨mid, hstep, htailRep⟩
    exact (ih htailSafe htailRep).trans (hframe ⟨_, e⟩ s mid r he hstep)

theorem handled_prefix_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {p : ApiTrace A}
    (hsafe : HandledTreeSafe profile step s t)
    (htrace : ITree.HasTrace t p)
    (hrep : ReplayTo step s p s') :
    protectedState s' = protectedState s :=
  replayTo_preserves_protected hframe
    (hsafe p ⟨htrace, (replayTo_iff_replay step s p).mp ⟨s', hrep⟩⟩)
    hrep

theorem handled_returnsTo_preserves_protected {S P A : Type} {profile : AuthorityProfile}
    {step : ApiHandler S} {protectedState : S → P}
    (hframe : FrameContract profile step protectedState)
    {s s' : S} {t : ApiTree A} {a : A}
    (hsafe : HandledTreeSafe profile step s t)
    (hret : ITree.ReturnsTo step s t s' a) :
    protectedState s' = protectedState s := by
  induction hret with
  | ret x a => rfl
  | @exchange R e k r x y z a hstep hrest ih =>
    have he : EventAllowed profile ⟨R, e⟩ :=
      hsafe (.request e) ⟨ITree.hasTrace_vis_request e k, trivial⟩
    have hnext : HandledTreeSafe profile step y (k r) := fun q hq =>
      (hsafe (.exchange e r q)
        ⟨(ITree.hasTrace_vis_exchange_iff e k r q).mpr hq.1, ⟨y, hstep, hq.2⟩⟩).2
    exact (ih hnext).trans (hframe ⟨R, e⟩ x y r he hstep)

theorem openReadCloseSession_safe (db : DbId) (sql : String) :
    TreeSafe (readOnlyProfile db) (openReadCloseSession db sql) := by
  unfold openReadCloseSession
  apply treeSafe_bind
  · exact treeSafe_vis (by simp [EventAllowed, checkEvent, readOnlyProfile])
      (fun _ => treeSafe_ret _ _)
  · intro openRes
    cases openRes with
    | error err => exact treeSafe_ret _ _
    | ok conn =>
      apply treeSafe_bind
      · exact treeSafe_vis (by simp [EventAllowed, checkEvent, readOnlyProfile])
          (fun _ => treeSafe_ret _ _)
      · intro prepRes
        cases prepRes with
        | error err =>
          apply treeSafe_bind
          · exact treeSafe_vis (by simp [EventAllowed, checkEvent])
              (fun _ => treeSafe_ret _ _)
          · intro _
            exact treeSafe_ret _ _
        | ok stmt =>
          apply treeSafe_bind
          · exact treeSafe_vis (by simp [EventAllowed, checkEvent, readOnlyProfile])
              (fun _ => treeSafe_ret _ _)
          · intro stepRes
            apply treeSafe_bind
            · exact treeSafe_vis (by simp [EventAllowed, checkEvent])
                (fun _ => treeSafe_ret _ _)
            · intro _
              apply treeSafe_bind
              · exact treeSafe_vis (by simp [EventAllowed, checkEvent])
                  (fun _ => treeSafe_ret _ _)
              · intro _
                cases stepRes with
                | error _ => exact treeSafe_ret _ _
                | ok outcome =>
                  cases outcome <;> exact treeSafe_ret _ _

theorem guardedDeniedWriteSession_safe (db : DbId) (offset : Nat) (bytes : List UInt8) :
    TreeSafe (readOnlyProfile db) (guardedDeniedWriteSession db offset bytes) := by
  unfold guardedDeniedWriteSession
  apply treeSafe_bind (treeSafe_guardedCall _ _)
  intro openRes
  cases openRes with
  | error _ => exact treeSafe_ret _ _
  | ok conn =>
    apply treeSafe_bind (treeSafe_guardedCall _ _)
    intro writeRes
    apply treeSafe_bind (treeSafe_guardedCall _ _)
    intro _
    exact treeSafe_ret _ _

theorem referenceHandler_frameContract (db : DbId) :
    FrameContract (readOnlyProfile db) referenceHandler ReferenceState.protectedDb := by
  intro q s s' r hall hstep
  rcases q with ⟨R, e⟩
  cases e with
  | openDb target mode =>
    cases mode with
    | readOnly =>
      cases r with
      | error _ => simp [referenceHandler] at hstep; rw [hstep]
      | ok _ => rcases hstep with ⟨_, _, rfl⟩; rfl
    | readWrite =>
      by_cases h : target = db <;> simp [EventAllowed, checkEvent, readOnlyProfile, h] at hall
  | prepare conn target sql =>
    cases r with
    | error _ => simp [referenceHandler] at hstep; rw [hstep]
    | ok _ => rcases hstep with ⟨_, _, _, rfl⟩; rfl
  | stepRead stmt target =>
    cases r with
    | error _ => simp [referenceHandler] at hstep; rw [hstep]
    | ok _ => rcases hstep with ⟨_, rfl⟩; rfl
  | finalize stmt =>
    cases r with
    | error _ => simp [referenceHandler] at hstep; rw [hstep]
    | ok _ => rcases hstep with ⟨_, rfl⟩; rfl
  | closeDb conn =>
    cases r with
    | error _ => simp [referenceHandler] at hstep; rw [hstep]
    | ok _ => rcases hstep with ⟨_, rfl⟩; rfl
  | writeDb conn target off bytes =>
    by_cases h : target = db <;> simp [EventAllowed, checkEvent, readOnlyProfile, h] at hall
  | attachDb conn target schema =>
    simp [EventAllowed, checkEvent, readOnlyProfile] at hall
  | loadExtension conn path =>
    simp [EventAllowed, checkEvent, readOnlyProfile] at hall
  | hostEffect kind =>
    simp [EventAllowed, checkEvent, readOnlyProfile] at hall

end Silmaril.Proofs.Semantics.SQLite.Isolation.Api
