module

public import Silmaril.Games.Abstract.SessionCat.Thms
public import Silmaril.Proofs.Games.Abstract.SessionRoute.Handler

/-!
# A session served to a one-call handler (proofs)

`threadS_comp_callH`: the session of `t` composed with the one-call handler `callH g f` is the
session of `mapS g f t`. The handler's strategy is the session of `callS g f`
(`threadS_callS`), so the composite is the linked session `threadS (linkS t (callS g f))`
(`SessionLink.comp_threadS`). A linked round at `a'` serves the single call of `callS g f` by
one round of `t` at `g a'` (`mem_linkS_callS`); the linked pending calls and streams are those
of `t` at `g a'`. So the first store component is a bisimulation (`obsEq_linkS_callS`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionRoute

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionCat
  Silmaril.Games.Abstract.SessionRoute

universe u

section CallS

variable {E : Sig.{u}} {A B : Type u} {g : A → E.Op} {f : (a : A) → E.Ar (g a) → B ⊕ PUnit.{u + 1}}

theorem retDet_callS : RetDet (callS g f) := by
  rintro s a c c' b b' s₁ s₁' ⟨y, hy⟩ ⟨y', hy'⟩
  simp only [Prod.mk.injEq, End.ret.injEq] at hy hy'
  obtain ⟨rfl, rfl, -⟩ := hy
  obtain ⟨rfl, rfl, -⟩ := hy'
  exact ⟨rfl, fun h => by cases h; rfl⟩

theorem noPlainTrap_callS : NoPlainTrap (callS g f) := by
  rintro s a c ⟨y, hy⟩
  cases (Prod.ext_iff.1 hy).2

end CallS

variable {E : Sig.{u}} {S A A' B B' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
  {g : A' → A} {f : A' → B ⊕ PUnit.{u + 1} → B' ⊕ PUnit.{u + 1}}

theorem streamTake_inj {α : Type u} {ω ω' : ℕ → α} (h : ∀ k, streamTake ω k = streamTake ω' k) :
    ω = ω' := by
  funext k
  have := congrArg (fun l => l[k]?) (h (k + 1))
  simp only [streamTake, List.getElem?_ofFn] at this
  simpa using this

theorem mem_mapS {s : S} {a' : A'} {x : List (Call E) × End S (B' ⊕ PUnit.{u + 1})} :
    x ∈ (mapS g f t).1 s a' ↔ ∃ e, (x.1, e) ∈ t.1 s (g a') ∧ x.2 = mapEnd (f a') e := by
  constructor
  · rintro ⟨⟨d, e⟩, h, rfl⟩
    exact ⟨e, h, rfl⟩
  · rintro ⟨e, h, he⟩
    exact ⟨(x.1, e), h, Prod.ext rfl he.symm⟩

theorem agree_map {S S' B B' : Type u} (k : End S B → End S' B') {c₁ c₂ : List (Call E)}
    {e₁ e₂ : End S B} (h : AFun.Agree c₁ e₁ c₂ e₂) : AFun.Agree c₁ (k e₁) c₂ (k e₂) := by
  induction c₁ generalizing c₂ with
  | nil =>
    rcases c₂ with _ | ⟨⟨m, n⟩, c₂⟩
    · exact congrArg k h
    · exact h.elim
  | cons x c₁ ih =>
    rcases c₂ with _ | ⟨⟨m, n⟩, c₂⟩
    · exact h.elim
    · obtain ⟨m₁, n₁⟩ := x
      exact ⟨h.1, fun hn => ih (h.2 hn)⟩

theorem noPlainTrap_mapS (h : NoPlainTrap t) : NoPlainTrap (mapS g f t) := by
  intro s a c hc
  obtain ⟨e, he, hx⟩ := mem_mapS.1 hc
  cases e with
  | trap => exact h _ _ _ he
  | ret => cases hx
  | div => cases hx

theorem retDet_mapS (h : RetDet t) : RetDet (mapS g f t) := by
  intro s a c c' b b' s₁ s₁' hc hc'
  obtain ⟨e, he, hx⟩ := mem_mapS.1 hc
  obtain ⟨e', he', hx'⟩ := mem_mapS.1 hc'
  cases e with
  | trap => cases hx
  | div => cases hx
  | ret x s₂ =>
    cases e' with
    | trap => cases hx'
    | div => cases hx'
    | ret x' s₂' =>
      dsimp only at hx hx' he he'
      rw [hx, hx']
      exact agree_map (mapEnd (f a)) (h _ _ _ _ _ _ _ _ he he')

/-- **A linked round of a one-call client**: one round of the server at `g a'`, its answer
mapped, or a divergence of the server there. -/
theorem mem_linkS_callS {s : S} {a' : A'}
    {x : List (Call E) × End (S × PUnit.{u + 1}) (B' ⊕ PUnit.{u + 1})} :
    x ∈ (linkS t (callS (E := sig1 A B) g f)).1 (s, PUnit.unit) a' ↔
      (∃ c n s₁, (c, End.ret n s₁) ∈ t.1 s (g a') ∧ x = (c, End.ret (f a' n) (s₁, PUnit.unit))) ∨
      (∃ c, (c, End.div) ∈ t.1 s (g a') ∧ x = (c, End.div)) := by
  constructor
  · rintro (⟨rs, s₁, e, hrs, ⟨n, hn⟩, rfl⟩ | ⟨rs, s₁, a, c, hrs, ha, hc, rfl⟩ | ⟨ω, hω, -⟩)
    · obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 hn
      rcases rs with _ | ⟨⟨a, c, b⟩, _ | _⟩ <;> simp [served] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      obtain _ | ⟨hr, hrs'⟩ := hrs
      cases hrs'
      exact .inl ⟨c, b, _, hr, by simp [servedLog, linkEnd]⟩
    · obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 (mem_satP_callS ha)
      simp only [served, List.map_eq_nil_iff] at h₁
      subst h₁
      cases hrs
      exact .inr ⟨c, hc, by simp [servedLog]⟩
    · exact hω.elim
  · rintro (⟨c, n, s₁, h, rfl⟩ | ⟨c, h, rfl⟩)
    · exact .inl ⟨[(g a', c, n)], s₁, End.ret (f a' n) PUnit.unit, .cons h (.nil _), ⟨n, rfl⟩,
        by simp [servedLog, linkEnd]⟩
    · exact .inr (.inl ⟨[], s, g a', c, .nil _, self_mem_satP_callS _ _, h, by simp [servedLog]⟩)

theorem satP_mapS (s : S) (a' : A') : satP (mapS g f t) s a' = satP t s (g a') := by
  ext x
  refine or_congr Iff.rfl (or_congr Iff.rfl (or_congr ?_ Iff.rfl))
  constructor
  · rintro ⟨d, e, h, hd⟩
    obtain ⟨e', h', -⟩ := mem_mapS.1 h
    exact ⟨d, e', h', hd⟩
  · rintro ⟨d, e, h, hd⟩
    exact ⟨d, mapEnd (f _) e, mem_mapS.2 ⟨e, h, rfl⟩, hd⟩

/-- **The first store component is a bisimulation** between the linked triple of a one-call
client and the mapped server. -/
theorem obsEq_linkS_callS (hnt : NoPlainTrap t) (s : S) :
    ObsEq (linkS t (callS (E := sig1 A B) g f)) (mapS g f t) (s, PUnit.unit) s := by
  refine ⟨fun σ s' => σ = (s', PUnit.unit), ?_, rfl⟩
  rintro σ s rfl
  refine ⟨fun a' c => ?_, fun a' c => ?_, ?_, ?_, fun a' c b σ₁ h => ?_, fun a' c b s₁ h => ?_⟩
  · rw [mem_linkS_callS, mem_mapS]
    constructor
    · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩) <;> cases (Prod.mk.inj h).2
    · rintro ⟨e, h, he⟩
      cases e with
      | ret => cases he
      | div => cases he
      | trap => exact (hnt _ _ _ h).elim
  · rw [mem_linkS_callS, mem_mapS]
    constructor
    · rintro (⟨_, _, _, _, h⟩ | ⟨d, hd, h⟩)
      · cases (Prod.mk.inj h).2
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h
        exact ⟨.div, hd, rfl⟩
    · rintro ⟨e, h, he⟩
      cases e with
      | ret => cases he
      | trap => cases he
      | div => exact .inr ⟨c, h, rfl⟩
  · rw [saturated_iff.1 saturated_linkS]
    funext a'
    rw [satP_mapS]
    ext x
    constructor
    · rintro ⟨rs, s₁, a, c, hrs, ha, hc, hx⟩
      obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 (mem_satP_callS ha)
      simp only [served, List.map_eq_nil_iff] at h₁
      subst h₁
      cases hrs
      simp only [servedLog, List.flatMap_nil, List.nil_append] at hx
      rcases x with ⟨x₁, x₂⟩
      simp only at hx
      subst hx
      exact hc
    · intro hx
      exact ⟨[], s, g a', x.1, .nil _, self_mem_satP_callS _ _, hx, by simp [servedLog]⟩
  · funext a'
    ext ω
    constructor
    · rintro (⟨rs, s₁, a, ω', hrs, ha, hω', hk⟩ | ⟨ω', hω', -⟩)
      · obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 (mem_satP_callS ha)
        simp only [served, List.map_eq_nil_iff] at h₁
        subst h₁
        cases hrs
        have : ω = ω' := streamTake_inj fun k => by simpa [servedLog] using hk k
        subst this
        exact hω'
      · exact hω'.elim
    · intro hω
      exact .inl ⟨[], s, g a', ω, .nil _, self_mem_satP_callS _ _, hω, fun k => by
        simp [servedLog]⟩
  · rcases (mem_linkS_callS.1 h) with ⟨d, n, s₁, hd, hx⟩ | ⟨d, _, hx⟩
    · simp only [Prod.mk.injEq, End.ret.injEq] at hx
      obtain ⟨rfl, rfl, rfl⟩ := hx
      exact ⟨s₁, mem_mapS.2 ⟨.ret n s₁, hd, rfl⟩, rfl⟩
    · cases (Prod.mk.inj hx).2
  · obtain ⟨e, hd, he⟩ := mem_mapS.1 h
    dsimp only at hd he
    cases e with
    | trap => cases he
    | div => cases he
    | ret n s₂ =>
      simp only [mapEnd, End.ret.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, mem_linkS_callS.2 (.inl ⟨c, n, _, hd, rfl⟩), rfl⟩

/-- **A session served to a one-call handler is the session of the mapped triple.** -/
theorem threadS_comp_callH (hnt : NoPlainTrap t) (ht : RetDet t) (s : S) :
    (threadS t s).comp (DStrategy.ofHandler (callH (E := sig1 A B) g f)) =
      threadS (mapS g f t) s := by
  rw [← threadS_callS, comp_threadS hnt (storeDet_of_retDet ht)
    (storeDet_of_retDet (retDet_linkS ht retDet_callS))]
  exact threadS_eq_of_obsEq (obsEq_linkS_callS hnt s)

end Silmaril.Proofs.Games.Abstract.SessionRoute
