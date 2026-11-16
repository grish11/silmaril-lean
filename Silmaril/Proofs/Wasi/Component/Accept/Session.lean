module

public import Silmaril.Wasi.Component.Accept.Session.Defs
public import Silmaril.Wasi.Component.Accept.Stream.Thms
public import Silmaril.Wasi.World.Exports.Thms
public import Silmaril.Semantics.Acceptors.Thms

/-!
# Incremental components as client sessions: proofs

By induction on the alternating, matched export events of a legal play
(`Silmaril.Wasi.ExportAlt`). Only export events contribute to sessions, protocol events and
answers. The export events of a legal play come in matched pairs `call f args`, `ret f args r`,
the last call possibly open. So each pair contributes in lockstep:

* to the session, at most one call;
* to the protocol events, at most one event;
* to the answers, at most one answer.

A completed `query()` pair contributes `query (answerOf r)` to the session, the event `query`,
and the answer `b` exactly when `answerOf r = some b`. Imports and host answers may occur
anywhere between the call and its return. They are not export events and contribute nothing.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasi.Component.Accept

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Accept Silmaril.Formats.Accept
open Silmaril.Accept (Call)
open Silmaril.Wasm.Component (Val)

variable (fns : StreamFns) (L : ByteLang) [DecidablePred (· ∈ L)]

/-- The pending input after a session prefix. -/
def pendAfter : List UInt8 → List (Call (List UInt8) (Option Bool)) → List UInt8
  | w, [] => w
  | w, .feed c :: p => pendAfter (w ++ c) p
  | _, .reset :: p => pendAfter [] p
  | w, .query _ :: p => pendAfter w p

/-- The claim for a list of export events. -/
def Claim (X : List WEv) : Prop :=
  ∀ (S : List (Call (List UInt8) (Option Bool))) (b : Bool) (w : List UInt8),
    X.filterMap fns.session = S ++ [.query (some b)] → Call.query none ∉ S →
    X.filterMap fns.answer <+: Silmaril.Acceptor.specFrom L w (X.filterMap fns.event) →
    b = decide (pendAfter w S ∈ L)

/-- The motive over the open call. -/
def Motive : Option (FnName × List Val) → List WEv → Prop
  | none, X => Claim fns L X
  | some (f, a), X => Claim fns L (.call f a :: X)

theorem session_call_ne_query (f : FnName) (a : List Val) (q : Option Bool) :
    fns.session (.call f a) ≠ some (.query q) := by
  simp only [StreamFns.session]
  split_ifs
  · cases args1 bytes? a <;> simp
  · simp
  · simp

theorem filterMap_single_call {f : FnName} {a : List Val} {S : List (Call (List UInt8) (Option Bool))}
    {b : Bool} : [WEv.call f a].filterMap fns.session ≠ S ++ [.query (some b)] := by
  intro h
  simp only [List.filterMap_cons, List.filterMap_nil] at h
  cases hc : fns.session (.call f a) with
  | none => rw [hc] at h; have := congrArg List.length h; simp at this
  | some x =>
    rw [hc] at h
    rcases S with _ | ⟨y, S⟩
    · simp only [List.nil_append, List.cons.injEq, and_true] at h
      exact session_call_ne_query fns f a _ (h ▸ hc)
    · have := congrArg List.length h; simp at this

theorem motive_of_alt (hd : fns.Distinct) {o : Option (FnName × List Val)} {X : List WEv}
    (h : ExportAlt o X) : Motive fns L o X := by
  obtain ⟨hpq, hpr, hqr⟩ := hd
  induction h with
  | nil o =>
    rcases o with _ | ⟨f, a⟩
    · intro S b w hs
      have := congrArg List.length hs; simp at this
    · intro S b w hs
      exact absurd hs (filterMap_single_call fns)
  | call f a _ ih => exact ih
  | ret f a r hrest ih =>
    intro S b w hs hS hp
    have e3 : fns.answer (.call f a) = none := rfl
    by_cases hf : f = fns.process
    · subst hf
      have e0 : fns.session (.call fns.process a) = (args1 bytes? a).map .feed := by
        simp [StreamFns.session]
      have e0' : fns.event (.call fns.process a) = (args1 bytes? a).map .process := by
        simp [StreamFns.event]
      have e1 : fns.session (.ret fns.process a r) = none := by
        simp [StreamFns.session, hpq]
      have e2 : fns.answer (.ret fns.process a r) = none := by
        unfold StreamFns.answer; split <;> simp_all
      cases hc : args1 bytes? a with
      | none =>
        simp only [List.filterMap_cons, e0, e0', e1, e2, e3, hc, Option.map_none] at hs hp
        exact ih S b w hs hS hp
      | some c =>
        simp only [List.filterMap_cons, e0, e0', e1, e2, e3, hc, Option.map_some] at hs hp
        rcases S with _ | ⟨x, S'⟩
        · simp at hs
        · simp only [List.cons_append, List.cons.injEq] at hs
          obtain ⟨rfl, hs⟩ := hs
          simp only [Silmaril.Acceptor.specFrom] at hp
          exact ih S' b (w ++ Silmaril.ChunkView.toList c) hs (fun h => hS (by simp [h])) hp
    by_cases hq : f = fns.query
    · subst hq
      have e1 : fns.session (.call fns.query a) = none := by
        simp [StreamFns.session, Ne.symm hpq, hqr]
      by_cases ha : a = []
      · subst ha
        have e4 : fns.event (.call fns.query []) = some .query := by
          simp [StreamFns.event, Ne.symm hpq]
        have e5 : fns.session (.ret fns.query [] r) = some (.query (answerOf r)) := by
          simp [StreamFns.session]
        simp only [List.filterMap_cons, e1, e3, e4, e5] at hs hp
        rcases S with _ | ⟨x, S'⟩
        · simp only [List.nil_append, List.cons.injEq] at hs
          obtain ⟨hx, hrest'⟩ := hs
          have hr : r = some [.bool b] := by
            unfold answerOf at hx; split at hx <;> simp_all
          subst hr
          simp [StreamFns.answer, Silmaril.Acceptor.specFrom, Silmaril.Acceptor.member] at hp
          simp only [pendAfter]
          exact hp.1.trans (decide_eq_decide.2 Iff.rfl)
        · simp only [List.cons_append, List.cons.injEq] at hs
          obtain ⟨rfl, hs⟩ := hs
          have hne : answerOf r ≠ none := fun h => hS (by simp [h])
          obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.1 hne
          have hr : r = some [.bool b'] := by
            unfold answerOf at hb'; split at hb' <;> simp_all
          subst hr
          simp [StreamFns.answer, Silmaril.Acceptor.specFrom] at hp
          exact ih S' b w hs (fun h => hS (by simp [h])) hp.2
      · have e4 : fns.event (.call fns.query a) = none := by
          simp [StreamFns.event, Ne.symm hpq, hqr, ha]
        have e5 : fns.session (.ret fns.query a r) = none := by simp [StreamFns.session, ha]
        have e6 : fns.answer (.ret fns.query a r) = none := by
          unfold StreamFns.answer; split <;> simp_all
        simp only [List.filterMap_cons, e1, e3, e4, e5, e6] at hs hp
        exact ih S b w hs hS hp
    by_cases hr : f = fns.reset
    · subst hr
      have e1 : fns.session (.ret fns.reset a r) = none := by
        simp [StreamFns.session, Ne.symm hqr]
      have e2 : fns.answer (.ret fns.reset a r) = none := by
        unfold StreamFns.answer; split <;> simp_all
      by_cases ha : a = []
      · subst ha
        have e4 : fns.event (.call fns.reset []) = some .reset := by
          simp [StreamFns.event, Ne.symm hpr, Ne.symm hqr]
        have e5 : fns.session (.call fns.reset []) = some .reset := by
          simp [StreamFns.session, Ne.symm hpr]
        simp only [List.filterMap_cons, e1, e2, e3, e4, e5] at hs hp
        rcases S with _ | ⟨x, S'⟩
        · simp at hs
        · simp only [List.cons_append, List.cons.injEq] at hs
          obtain ⟨rfl, hs⟩ := hs
          simp only [Silmaril.Acceptor.specFrom] at hp
          exact ih S' b [] hs (fun h => hS (by simp [h])) hp
      · have e4 : fns.event (.call fns.reset a) = none := by
          simp [StreamFns.event, Ne.symm hpr, Ne.symm hqr, ha]
        have e5 : fns.session (.call fns.reset a) = none := by
          simp [StreamFns.session, Ne.symm hpr, ha]
        simp only [List.filterMap_cons, e1, e2, e3, e4, e5] at hs hp
        exact ih S b w hs hS hp
    · have e1 : fns.session (.ret f a r) = none := by simp [StreamFns.session, hq]
      have e2 : fns.answer (.ret f a r) = none := by
        unfold StreamFns.answer; split <;> simp_all
      have e4 : fns.event (.call f a) = none := by simp [StreamFns.event, hf, hq, hr]
      have e5 : fns.session (.call f a) = none := by simp [StreamFns.session, hf, hr]
      simp only [List.filterMap_cons, e1, e2, e3, e4, e5] at hs hp
      exact ih S b w hs hS hp

theorem pendAfter_append (w : List UInt8) (p q : List (Call (List UInt8) (Option Bool))) :
    pendAfter w (p ++ q) = pendAfter (pendAfter w p) q := by
  induction p generalizing w with
  | nil => rfl
  | cons x p ih => cases x <;> simp [pendAfter, ih]

theorem pendAfter_feeds (w : List UInt8) (as : List (List UInt8)) :
    pendAfter w (as.map .feed) = w ++ as.flatten := by
  induction as generalizing w with
  | nil => simp [pendAfter]
  | cons c as ih => simp [pendAfter, ih, List.append_assoc]

theorem pendAfter_reset (w : List UInt8) (p : List (Call (List UInt8) (Option Bool))) :
    pendAfter w (p ++ [.reset]) = [] := by
  rw [pendAfter_append]; rfl

theorem filterMap_exportEvents {β : Type} (g : WEv → Option β)
    (hg : ∀ e, e.isExp = false → g e = none) (t : List WEv) :
    t.filterMap g = (exportEvents t).filterMap g := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    rw [exportEvents_cons]
    by_cases he : e.isExp = true
    · simp [he, List.filterMap_cons, ih]
    · have := hg e (by simpa using he)
      simp [he, this, ih]

theorem session_nonExp (e : WEv) (h : e.isExp = false) : fns.session e = none := by
  cases e <;> simp_all [WEv.isExp, StreamFns.session]

theorem event_nonExp (e : WEv) (h : e.isExp = false) : fns.event e = none := by
  cases e <;> simp_all [WEv.isExp, StreamFns.event]

theorem answer_nonExp (e : WEv) (h : e.isExp = false) : fns.answer e = none := by
  cases e <;> simp_all [WEv.isExp, StreamFns.answer]

/-- **The claim holds of every legal play.** -/
theorem claim_of_legal (hd : fns.Distinct) {I X : Set FnName} {s : List (Move (nsig I) (nsig X))}
    (hs : Legal s) : Claim fns L (wtrace s) := by
  intro S b w h1 h2 h3
  have hm := motive_of_alt fns L hd (exportAlt_of_legal hs)
  rw [filterMap_exportEvents _ (session_nonExp fns)] at h1
  rw [filterMap_exportEvents _ (answer_nonExp fns),
    filterMap_exportEvents _ (event_nonExp fns)] at h3
  exact hm S b w h1 h2 h3

variable {fns L}

/-- **Fresh sessions of a correct component answer by membership.** -/
theorem freshFeedsQuery_sound (hd : fns.Distinct) {I X : Set FnName}
    {σ : Strategy (nsig I) (nsig X)} (hc : StreamCorrect fns σ L) {as : List (List UInt8)}
    {b : Bool} (h : (as, some b) ∈ Silmaril.Accept.freshFeedsQuery (sessionTraces fns σ)) :
    b = decide (as.flatten ∈ L) := by
  obtain ⟨_, ⟨s, hs, rfl⟩, ht⟩ := h
  have := claim_of_legal fns L hd (σ.legal hs) (as.map .feed) b [] ht (by simp)
    (hc _ ⟨s, hs, rfl⟩)
  rwa [pendAfter_feeds, List.nil_append] at this

/-- **Sessions after a reset**, when every completed query returns a `bool`. -/
theorem feedsQuery_sound (hd : fns.Distinct) {I X : Set FnName}
    {σ : Strategy (nsig I) (nsig X)} (hc : StreamCorrect fns σ L) (ht : QueryTotal fns σ)
    {as : List (List UInt8)} {b : Bool}
    (h : (as, some b) ∈ Silmaril.Accept.feedsQuery (sessionTraces fns σ)) :
    b = decide (as.flatten ∈ L) := by
  obtain ⟨-, pre, hpre, hT⟩ := h
  obtain ⟨_, ⟨s, hs, rfl⟩, hst⟩ := hT
  have hS : Call.query none ∉ pre ++ as.map .feed := fun hm =>
    ht _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩ (by rw [hst]; simp only [List.mem_append] at hm ⊢; tauto)
  have := claim_of_legal fns L hd (σ.legal hs) (pre ++ as.map .feed) b []
    (by simpa using hst) hS (hc _ ⟨s, hs, rfl⟩)
  rw [pendAfter_append, pendAfter_feeds] at this
  rcases hpre with rfl | ⟨p, rfl⟩
  · simp only [pendAfter, List.nil_append] at this
    exact this.trans (decide_eq_decide.2 Iff.rfl)
  · rwa [pendAfter_reset, List.nil_append] at this

end Silmaril.Proofs.Wasi.Component.Accept
