module

public import Silmaril.Proofs.Games.Abstract.SessionLinkAssoc.Serve
public import Silmaril.Games.Abstract.SessionLink.Thms

/-!
# Linking sessions: rounds of a linked triple (proofs)

A returning round of `linkS t u` is a returning round of the client `u` whose calls are served by
rounds of `t` (`ret_linkS_iff`). Hence a list of linked rounds is a list of client rounds and a
list of server rounds serving their calls (`rounds_linkS_fwd`, `rounds_linkS_bwd`), and a coherent
service by `linkS t u` is a coherent service by `u` whose rounds are served by blocks of rounds of
`t` (`infServe_linkS_fwd`, `infServe_linkS_bwd`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkAssoc

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.SessionLink

universe u

variable {E : Sig.{u}} {S S' A B A' B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {u : ObsTriple (sig1 A B) S' A' (B' ⊕ PUnit.{u + 1})}

theorem linkEnd_eq_ret {s : S} {e : End S' (B' ⊕ PUnit.{u + 1})} {x : B' ⊕ PUnit.{u + 1}}
    {σ : S × S'} (h : linkEnd s e = .ret x σ) : e = .ret x σ.2 ∧ s = σ.1 := by
  cases e with
  | ret y s' => simp only [linkEnd, End.ret.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | trap => cases h
  | div => cases h

theorem linkEnd_eq_div {s : S} {e : End S' (B' ⊕ PUnit.{u + 1})} (h : linkEnd s e = .div) :
    e = .div := by
  cases e with
  | ret => cases h
  | trap => cases h
  | div => rfl

/-- **A returning linked round**: a returning client round, its calls served by server rounds. -/
theorem ret_linkS_iff {σ σ' : S × S'} {a' : A'} {c : List (Call E)} {y : B' ⊕ PUnit.{u + 1}} :
    (c, End.ret y σ') ∈ (linkS t u).1 σ a' ↔
      ∃ rt, Rounds t σ.1 rt σ'.1 ∧ (served rt, End.ret y σ'.2) ∈ u.1 σ.2 a' ∧
        c = servedLog rt := by
  constructor
  · rintro (⟨rs, s₁, e, hr, he, hx⟩ | ⟨_, _, _, _, _, _, _, hx⟩ | ⟨_, _, _, _, _, _, _, hx⟩)
    · obtain ⟨hc, he'⟩ := Prod.mk.inj hx
      obtain ⟨rfl, rfl⟩ := linkEnd_eq_ret he'.symm
      exact ⟨rs, hr, he, hc⟩
    all_goals cases (Prod.mk.inj hx).2
  · rintro ⟨rt, hr, hu, rfl⟩
    exact .inl ⟨rt, σ'.1, .ret y σ'.2, hr, hu, rfl⟩

/-- The call prefixes of a linked triple are its pending calls. -/
theorem satP_linkS_iff {σ : S × S'} {a' : A'} {x : List (Call E) × E.Op} :
    x ∈ satP (linkS t u) σ a' ↔ ∃ rt s₁ a c, Rounds t σ.1 rt s₁ ∧ (served rt, a) ∈ satP u σ.2 a' ∧
      (c, x.2) ∈ satP t s₁ a ∧ x.1 = servedLog rt ++ c := by
  rw [saturated_iff.1 (saturated_linkS (t := t) (u := u))]
  rfl

/-- **Linked rounds** are client rounds served by server rounds. -/
theorem rounds_linkS_fwd {σ σ' : S × S'} {rs : List (A' × List (Call E) × (B' ⊕ PUnit.{u + 1}))}
    (h : Rounds (linkS t u) σ rs σ') :
    ∃ rt ru, Rounds t σ.1 rt σ'.1 ∧ Rounds u σ.2 ru σ'.2 ∧ served rt = servedLog ru ∧
      served ru = served rs ∧ servedLog rt = servedLog rs := by
  induction h with
  | nil => exact ⟨[], [], .nil _, .nil _, rfl, rfl, rfl⟩
  | @cons σ σ₁ σ₂ a c b rs hr _ ih =>
    obtain ⟨rt₀, h₀, hu₀, rfl⟩ := ret_linkS_iff.1 hr
    obtain ⟨rt, ru, ht, hu, h₁, h₂, h₃⟩ := ih
    exact ⟨rt₀ ++ rt, (a, served rt₀, b) :: ru, rounds_append h₀ ht, .cons hu₀ hu,
      by simp [h₁], by simp [h₂], by simp [h₃]⟩

/-- **Client rounds served by server rounds** are linked rounds. -/
theorem rounds_linkS_bwd {s₁ s₁' : S} {s₂ s₂' : S'}
    {rt : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    {ru : List (A' × List (Call (sig1 A B)) × (B' ⊕ PUnit.{u + 1}))}
    (ht : Rounds t s₁ rt s₁') (hu : Rounds u s₂ ru s₂') (h : served rt = servedLog ru) :
    ∃ rs, Rounds (linkS t u) (s₁, s₂) rs (s₁', s₂') ∧ served rs = served ru ∧
      servedLog rs = servedLog rt := by
  induction hu generalizing s₁ rt with
  | nil =>
    obtain rfl := served_eq_nil.1 h
    obtain rfl := rounds_nil_iff.1 ht
    exact ⟨[], .nil _, rfl, rfl⟩
  | @cons s s₃ s₄ a c b ru hr _ ih =>
    obtain ⟨rt₁, rt₂, rfl, h₁, h₂⟩ := served_eq_append h
    obtain ⟨sm, hr₁, hr₂⟩ := rounds_of_append ht
    obtain ⟨rs, hrs, hs₁, hs₂⟩ := ih hr₂ h₂
    exact ⟨(a, servedLog rt₁, b) :: rs, .cons (ret_linkS_iff.2 ⟨rt₁, hr₁, h₁ ▸ hr, rfl⟩) hrs,
      by simp [hs₁], by simp [hs₂]⟩

/-- **A coherent service by a linked triple** is a coherent client service whose rounds are
served by blocks of server rounds. -/
theorem infServe_linkS_fwd {s₁ : S} {s₂ : S'} {ω : ℕ → Call (sig1 A' B')}
    {l : ℕ → List (Call E)} {st : ℕ → S × S'} (h : InfServe (linkS t u) (s₁, s₂) ω l st) :
    ∃ rt : ℕ → List (A × List (Call E) × (B ⊕ PUnit.{u + 1})),
      (∀ k, Rounds t (st k).1 (rt k) (st (k + 1)).1) ∧
      InfServe u s₂ ω (fun k => served (rt k)) (fun k => (st k).2) ∧
      (∀ k, l k = servedLog (rt k)) ∧ (st 0).1 = s₁ := by
  choose rt h₁ h₂ h₃ using fun k => ret_linkS_iff.1 (h.step k)
  exact ⟨rt, h₁, ⟨congrArg Prod.snd h.zero, h₂⟩, h₃, congrArg Prod.fst h.zero⟩

/-- **A coherent client service whose calls are served coherently** is a coherent service by the
linked triple: the server rounds are cut along the client's rounds. -/
theorem infServe_linkS_bwd {s₁ : S} {s₂ : S'} {ω : ℕ → Call (sig1 A' B')}
    {lu : ℕ → List (Call (sig1 A B))} {stu : ℕ → S'} {ω'' : ℕ → Call (sig1 A B)}
    {lt : ℕ → List (Call E)} {stt : ℕ → S} (hu : InfServe u s₂ ω lu stu)
    (ht : InfServe t s₁ ω'' lt stt)
    (hpre : ∀ k, streamTake ω'' (logTake lu k).length = logTake lu k) :
    ∃ l st, InfServe (linkS t u) (s₁, s₂) ω l st ∧
      (∀ k, l k = logTake (fun j => lt ((logTake lu k).length + j)) (lu k).length) ∧
      ∀ k, logTake l k = logTake lt (logTake lu k).length := by
  set N := fun k => (logTake lu k).length with hN
  have hN1 : ∀ k, N (k + 1) = N k + (lu k).length := fun k => by
    simp [hN, logTake_succ]
  have hserved : ∀ k, served (streamTake (serveRounds ω'' lt (N k)) (lu k).length) = lu k := by
    intro k
    rw [served_serveRounds]
    have h₁ := hpre (k + 1)
    rw [show (logTake lu (k + 1)).length = N k + (lu k).length from hN1 k, streamTake_add,
      show streamTake ω'' (N k) = logTake lu k from hpre k, logTake_succ] at h₁
    exact List.append_cancel_left h₁
  refine ⟨fun k => servedLog (streamTake (serveRounds ω'' lt (N k)) (lu k).length),
    fun k => (stt (N k), stu k), ⟨?_, fun k => ?_⟩, fun k => ?_, fun k => ?_⟩
  · simp [hN, ht.zero, hu.zero]
  · refine ret_linkS_iff.2 ⟨_, ?_, ?_, rfl⟩
    · have := rounds_block ht (N k) (lu k).length
      rwa [← hN1] at this
    · rw [hserved]
      exact hu.step k
  · exact servedLog_serveRounds _ _ _ _
  · induction k with
    | zero => rfl
    | succ k ih =>
      rw [logTake_succ, ih, servedLog_serveRounds, show (logTake lu (k + 1)).length = N (k + 1)
        from rfl, hN1, logTake_add]

/-- **Blocks of server rounds serving infinitely many client calls** flatten into a coherent
server service of the concatenated calls. -/
theorem infServe_flat {s₁ : S} {rt : ℕ → List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    {st : ℕ → S} (h : ∀ k, Rounds t (st k) (rt k) (st (k + 1))) (h₀ : st 0 = s₁)
    (hunb : ∀ n, ∃ k, n ≤ (logTake (fun k => served (rt k)) k).length) :
    ∃ ω'' lt stt, InfServe t s₁ ω'' lt stt ∧
      (∀ k, streamTake ω'' (logTake (fun k => served (rt k)) k).length =
        logTake (fun k => served (rt k)) k) ∧
      ∀ k, logTake lt (logTake (fun k => served (rt k)) k).length =
        logTake (fun k => servedLog (rt k)) k := by
  have hlen : ∀ k, (logTake (fun k => served (rt k)) k).length =
      (streamTake rt k).flatten.length := fun k => by
    rw [← served_flatten, length_served]
  obtain ⟨ω'', lt, stt, hs, hk⟩ := flat_serve h fun n => by
    obtain ⟨k, hk⟩ := hunb (n + 1)
    exact ⟨k, by rw [← hlen]; omega⟩
  refine ⟨ω'', lt, stt, h₀ ▸ hs, fun k => ?_, fun k => ?_⟩
  · rw [hlen, (hk k).1, served_flatten]
  · rw [hlen, (hk k).2, servedLog_flatten]

end Silmaril.Proofs.Games.Abstract.SessionLinkAssoc
