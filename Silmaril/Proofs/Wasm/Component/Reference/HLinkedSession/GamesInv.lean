module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Games
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Games

/-!
# Plays of linked components with host imports: inverting the game lemmas

The converses of the layers of `HLinkedSession.Games` that `LinkedSessionAdeq.Games` does not
invert:

* **serving with lower calls** (`serveC_inv`, the converse of `cplay_comp_serveC`): complete
  rounds of `σ.comp τ`, with lower calls, are rounds of `τ` whose lower calls, all together and
  in order, are rounds of `σ` with their own lower calls, which are the visible ones
  (`serve_inv` is the case of `σ` without lower moves);
* **copycat** (`id_cs`, the converse of `cplay_id_calls`): each round of copycat is answered
  by the same call below;
* **mixed pairings** (`pair_mixed_inv`, the converse of `cplay_pair_mixed`): rounds of a
  pairing are rounds of its left and right components;
* rounds of a strategy without lower moves make no lower calls (`cs_nil_of_noInl`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq

variable {E F G : Sig.{0}}

/-! ## Serving with lower calls -/

/-- The lower calls of a round on top, answered by rounds below with lower calls of their own,
which are visible. -/
theorem subs_of_zip : ∀ (cs : List (Round F)) (S : List (CRound E F)) (X : List (Move F G))
    (p : List (Move E G)), Zip (cplay S) (callMoves cs ++ X) p →
    ∃ (subs S' : List (CRound E F)) (p' : List (Move E G)), cs = subs.map CRound.toRound ∧
      S = subs ++ S' ∧ p = callMoves (subs.flatMap (·.cs)) ++ p' ∧ Zip (cplay S') X p'
  | [], S, _, p, h => ⟨[], S, p, rfl, rfl, rfl, h⟩
  | ⟨m, n⟩ :: cs, S, X, p, h => by
    have h₀ : Zip (cplay S) (.inl (.ask m) :: .inl (.ans m n) :: (callMoves cs ++ X)) p := h
    obtain ⟨s', hs', h₁⟩ := zip_sync_of h₀ cplay_ne_inl'
    cases S with
    | nil => cases hs'
    | cons x S₀ =>
      obtain ⟨xq, xcs, xa⟩ := x
      have hs'' : Sum.inr (Ev.ask xq) :: (callMoves xcs ++ Sum.inr (Ev.ans xq xa) :: cplay S₀) =
          Sum.inr (Ev.ask m) :: s' := hs'
      simp only [List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq] at hs''
      obtain ⟨rfl, rfl⟩ := hs''
      obtain ⟨P', rfl, h₂⟩ := zip_calls_strip xcs h₁
      obtain ⟨hn, h₃⟩ := zip_sync h₂
      have hn' : xa = n := by simpa only [Ev.ans.injEq, heq_eq_eq, true_and] using hn
      subst hn'
      obtain ⟨subs, S', p', rfl, rfl, rfl, h₄⟩ := subs_of_zip cs S₀ X P' h₃
      refine ⟨⟨xq, xcs, xa⟩ :: subs, S', p', rfl, rfl, ?_, h₄⟩
      rw [List.flatMap_cons, callMoves_appendH, List.append_assoc]

/-- The rounds of a composite whose lower strategy serves the lower calls of the upper one. -/
theorem serve_of_zip : ∀ (U : List (CRound F G)) (S : List (CRound E F)) (p : List (Move E G)),
    Zip (cplay S) (cplay U) p →
    ∃ L : List (SRound E F G), U = L.map SRound.up ∧ S = L.flatMap (·.subs) ∧
      p = cplay (L.map SRound.vis)
  | [], S, p, h => by
    cases S with
    | nil =>
      cases h
      exact ⟨[], rfl, rfl, rfl⟩
    | cons x S =>
      exact ((zip_nil_right_inr h).1 _ List.mem_cons_self).elim
  | ⟨g, cs, a⟩ :: U, S, p, h => by
    have h₀ : Zip (cplay S) (.inr (.ask g) :: (callMoves cs ++ .inr (.ans g a) :: cplay U)) p := h
    obtain ⟨p₁, rfl, h₁⟩ := zip_right_of h₀ cplay_ne_inl'
    obtain ⟨subs, S', p', rfl, rfl, rfl, h₂⟩ := subs_of_zip cs S _ p₁ h₁
    obtain ⟨p'', rfl, h₃⟩ := zip_right_of h₂ cplay_ne_inl'
    obtain ⟨L, rfl, rfl, rfl⟩ := serve_of_zip U S' p'' h₃
    exact ⟨⟨g, subs, a⟩ :: L, rfl, rfl, rfl⟩

/-- **A strategy below serving the lower calls by rounds with lower calls**
(`cplay_comp_serveC` in reverse): complete rounds of `σ.comp τ` are rounds of `τ` whose lower
calls, all together and in order, are rounds of `σ`, their lower calls being the visible ones. -/
theorem serveC_inv {σ : Strategy E F} {τ : Strategy F G} {V : List (CRound E G)}
    (h : cplay V ∈ σ.comp τ) :
    ∃ L : List (SRound E F G), cplay (L.map SRound.up) ∈ τ ∧ cplay (L.flatMap (·.subs)) ∈ σ ∧
      L.map SRound.vis = V := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  obtain ⟨a', ha'⟩ := σ.legal hs
  obtain ⟨b', hb'⟩ := τ.legal ht
  obtain ⟨c', hc', hcomp⟩ := Strategy.zip_path hz Strategy.ZipCompat.idle ha' hb'
  have hc'' : c' = .idle := Path.det hc' (path_cplay V)
  subst hc''
  obtain ⟨rfl, rfl⟩ := zipCompat_idle hcomp
  obtain ⟨S, rfl⟩ := exists_cplay ha'
  obtain ⟨U, rfl⟩ := exists_cplay hb'
  obtain ⟨L, rfl, rfl, hp⟩ := serve_of_zip U S _ hz
  exact ⟨L, ht, hs, (cplay_inj hp).symm⟩

/-! ## Copycat -/

theorem id_run : ∀ (rs : List (CRound E E)) (y : (Handler.id E).toReduction.State),
    (Handler.id E).toReduction.toLTS.Run .idle (cplay rs) y → ∀ r ∈ rs, r.cs = [⟨r.q, r.a⟩]
  | [], _, _, _, hr => nomatch hr
  | ⟨q, cs, a⟩ :: rs, y, hrun, r, hr => by
    have h₀ : (Handler.id E).toReduction.toLTS.Run .idle
        (.inr (.ask q) :: (callMoves cs ++ .inr (.ans q a) :: cplay rs)) y := hrun
    obtain ⟨q', hq', h₁⟩ := run_idle_cons h₀
    cases hq'
    have h₁' : (Handler.id E).toReduction.toLTS.Run (.run q (.call q Prog.pure))
        (callMoves cs ++ .inr (.ans q a) :: cplay rs) y := h₁
    cases cs with
    | nil => cases (run_call_cons h₁').1
    | cons c cs =>
      obtain ⟨m, n⟩ := c
      obtain ⟨hm, h₂⟩ := run_call_cons (m := .inl (.ask m)) h₁'
      cases hm
      obtain ⟨n', hn, h₃⟩ := run_wait_cons h₂
      cases hn
      cases cs with
      | nil =>
        obtain ⟨ha, h₄⟩ := run_pure_cons h₃
        have ha' : a = n := by
          simpa only [Sum.inr.injEq, Ev.ans.injEq, heq_eq_eq, true_and] using ha
        subst ha'
        rcases List.mem_cons.mp hr with rfl | hr
        · rfl
        · exact id_run rs y h₄ r hr
      | cons c' cs' =>
        obtain ⟨m', n''⟩ := c'
        cases (run_pure_cons h₃).1

/-- **Copycat answers each round by the same call below** (`cplay_id_calls` in reverse). -/
theorem id_cs {rs : List (CRound E E)} (h : cplay rs ∈ Strategy.id E) :
    ∀ r ∈ rs, r.cs = [⟨r.q, r.a⟩] := by
  rw [← Strategy.ofHandler_id] at h
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.mp h
  exact id_run rs y hy

/-! ## Strategies without lower moves -/

/-- **The rounds of a play without lower moves make no lower calls.** -/
theorem cs_nil_of_noInl : ∀ {rs : List (CRound E F)}, NoInl (cplay rs) → ∀ r ∈ rs, r.cs = []
  | [], _, _, hr => nomatch hr
  | ⟨q, cs, a⟩ :: rs, h, r, hr => by
    have h' : NoInl (.inr (.ask q) :: (callMoves cs ++ .inr (.ans q a) :: cplay rs)) := h
    rcases List.mem_cons.mp hr with rfl | hr
    · cases cs with
      | nil => rfl
      | cons c cs =>
        obtain ⟨m, n⟩ := c
        exact (h' (.ask m) (List.mem_cons_of_mem _ (List.mem_append_left _
          (show Sum.inl (Ev.ask m) ∈ (callMoves (⟨m, n⟩ :: cs) : List (Move E F)) from
            List.mem_cons_self)))).elim
    · exact cs_nil_of_noInl (fun e he => h' e (List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_cons_of_mem _ he)))) r hr

/-! ## Mixed rounds of a pairing -/

/-- A round of a pairing, as a round of one of its two components. -/
def CRound.unlift {F₁ F₂ : Sig.{0}} : CRound E (F₁ ⊕ₛ F₂) → CRound E F₁ ⊕ CRound E F₂
  | ⟨.inl q, cs, a⟩ => .inl ⟨q, cs, a⟩
  | ⟨.inr q, cs, a⟩ => .inr ⟨q, cs, a⟩

theorem CRound.lift_unlift {F₁ F₂ : Sig.{0}} : ∀ r : CRound E (F₁ ⊕ₛ F₂), CRound.lift (CRound.unlift r) = r
  | ⟨.inl _, _, _⟩ => rfl
  | ⟨.inr _, _, _⟩ => rfl

theorem map_lift_unlift {F₁ F₂ : Sig.{0}} (D : List (CRound E (F₁ ⊕ₛ F₂))) :
    (D.map CRound.unlift).map CRound.lift = D := by
  induction D with
  | nil => rfl
  | cons r D ih => rw [List.map_cons, List.map_cons, CRound.lift_unlift, ih]

/-- **Rounds of a pairing are rounds of both components** (`cplay_pair_mixed` in reverse). -/
theorem pair_mixed_inv {F₁ F₂ : Sig.{0}} {σ₁ : Strategy E F₁} {σ₂ : Strategy E F₂}
    {D : List (CRound E (F₁ ⊕ₛ F₂))} (h : cplay D ∈ σ₁.pair σ₂) :
    cplay (lefts (D.map CRound.unlift)) ∈ σ₁ ∧ cplay (rights (D.map CRound.unlift)) ∈ σ₂ := by
  rw [← map_lift_unlift D] at h
  obtain ⟨-, h₁, h₂⟩ := h
  rw [halves_cplay_mixed] at h₁ h₂
  exact ⟨h₁, h₂⟩

theorem mem_lefts {F₁ F₂ : Sig.{0}} {r : CRound E F₁} :
    ∀ {l : List (CRound E F₁ ⊕ CRound E F₂)}, Sum.inl r ∈ l → r ∈ lefts l
  | [], h => nomatch h
  | .inl _ :: l, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_lefts h)
  | .inr _ :: l, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
    · exact mem_lefts (l := l) h

theorem mem_rights {F₁ F₂ : Sig.{0}} {r : CRound E F₂} :
    ∀ {l : List (CRound E F₁ ⊕ CRound E F₂)}, Sum.inr r ∈ l → r ∈ rights l
  | [], h => nomatch h
  | .inl _ :: l, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
    · exact mem_rights (l := l) h
  | .inr _ :: l, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_rights h)

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
