module

public import Silmaril.Games.Abstract.SessionLinkDead.Defs
public import Silmaril.Games.Abstract.StratSession.Thms

/-!
# The dead server: its session is the server's session

`threadS (deadS t) (some s₀) = threadS t s₀`. The finite plays are related by two simulations of
the threading automata up to `relMove`: the dead state `.dead` of `threadT t` is the idle dead
server `.idle none`, or, for a shadowed plain trap, the idle live server after the continuing
trap; a question after it (`.stuck a`) is a question to that server. Divergences and infinite
plays are compared on completed rounds (`StratSession.mem_div_iff`, `StratSession.mem_inf_iff`):
rounds of `deadS t` ending at a live store are rounds of `t`.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionLinkDead

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.SessionLinkDead

universe u

variable {E : Sig.{u}} {S A B : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

/-! ## Logs and call prefixes -/

theorem logs_deadBeh {s : S} {a : A} {d : List (Call E)} :
    (∃ e, (d, e) ∈ deadBeh t s a) ↔ ∃ e, (d, e) ∈ t.1 s a := by
  constructor
  · rintro ⟨_, ⟨_, _, h, -⟩ | ⟨h, -, -⟩ | ⟨h, -⟩⟩ <;> exact ⟨_, h⟩
  · rintro ⟨e, h⟩
    cases e with
    | ret y s₁ => exact ⟨_, .inl ⟨y, s₁, h, rfl⟩⟩
    | trap =>
      by_cases hs : ∃ s₁, (d, End.ret (.inr PUnit.unit) s₁) ∈ t.1 s a
      · obtain ⟨s₁, h₁⟩ := hs
        exact ⟨_, .inl ⟨_, s₁, h₁, rfl⟩⟩
      · exact ⟨_, .inr (.inl ⟨h, fun s₁ h₁ => hs ⟨s₁, h₁⟩, rfl⟩)⟩
    | div => exact ⟨_, .inr (.inr ⟨h, rfl⟩)⟩

theorem satP_deadS_some (s : S) : satP (deadS t) (some s) = satP t s := by
  funext a
  ext x
  constructor
  · rintro (h | h | ⟨d, e, he, hc⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · obtain ⟨e', he'⟩ := logs_deadBeh.1 ⟨e, he⟩
      exact .inr (.inr (.inl ⟨d, e', he', hc⟩))
    · exact .inr (.inr (.inr h))
  · rintro (h | h | ⟨d, e, he, hc⟩ | h)
    · exact .inl h
    · exact .inr (.inl h)
    · obtain ⟨e', he'⟩ := logs_deadBeh.2 ⟨e, he⟩
      exact .inr (.inr (.inl ⟨d, e', he', hc⟩))
    · exact .inr (.inr (.inr h))

theorem satP_deadS_none (a : A) : satP (deadS t) none a = ∅ := by
  ext x
  constructor
  · rintro (h | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩) <;> exact h.elim
  · intro h; exact h.elim

/-! ## Plain traps and determinism -/

theorem noPlainTrap_deadS : NoPlainTrap (deadS t) := by
  rintro (_ | s) a c h
  · exact h.elim
  · rcases h with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h

theorem storeDet_deadS (ht : StoreDet t) : StoreDet (deadS t) := by
  rintro (_ | s) a c b σ₁ σ₂ h₁ h₂
  · exact h₁.elim
  rcases h₁ with ⟨y, s₁, h₁, he₁⟩ | ⟨_, hn₁, he₁⟩ | ⟨_, he₁⟩ <;>
    rcases h₂ with ⟨y', s₂, h₂, he₂⟩ | ⟨_, hn₂, he₂⟩ | ⟨_, he₂⟩ <;>
    simp only [End.ret.injEq, reduceCtorEq] at he₁ he₂
  · obtain ⟨rfl, rfl⟩ := he₁
    obtain ⟨rfl, rfl⟩ := he₂
    rw [ht _ _ _ _ _ _ h₁ h₂]
  · obtain ⟨rfl, rfl⟩ := he₁
    obtain ⟨rfl, rfl⟩ := he₂
    exact (hn₂ _ h₁).elim
  · obtain ⟨rfl, rfl⟩ := he₁
    obtain ⟨rfl, rfl⟩ := he₂
    exact (hn₁ _ h₂).elim
  · rw [he₁.2, he₂.2]

/-- The end of a round of `deadS t` for an end of `t`. -/
def deadEnd : End S (B ⊕ PUnit.{u + 1}) → End (Option S) (B ⊕ PUnit.{u + 1})
  | .ret y s => .ret y (some s)
  | .trap => .ret (.inr PUnit.unit) none
  | .div => .div

theorem agree_map {S T B C : Type u} (f : End S B → End T C) :
    ∀ {c c' : List (Call E)} {e e'}, AFun.Agree c e c' e' → AFun.Agree c (f e) c' (f e')
  | [], [], _, _, h => congrArg f (h : _ = _)
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | ⟨_, _⟩ :: _, ⟨_, _⟩ :: _, _, _, h => ⟨h.1, fun hn => agree_map f (h.2 hn)⟩

theorem mem_deadBeh_iff {s : S} {a : A} {x : CallBeh E (Option S) (B ⊕ PUnit.{u + 1})}
    (h : x ∈ deadBeh t s a) : ∃ e, (x.1, e) ∈ t.1 s a ∧ x.2 = deadEnd e := by
  rcases h with ⟨_, _, h, he⟩ | ⟨h, -, he⟩ | ⟨h, he⟩ <;> exact ⟨_, h, he⟩

theorem det_deadS (ht : AFun.Det t.1) : AFun.Det (deadS t).1 := by
  rintro (_ | s) a x y hx hy
  · exact hx.elim
  obtain ⟨e, he, hxe⟩ := mem_deadBeh_iff hx
  obtain ⟨e', he', hye⟩ := mem_deadBeh_iff hy
  rw [hxe, hye]
  exact agree_map deadEnd (ht s a _ _ he he')

/-! ## Rounds -/

theorem rounds_deadS {s s₁ : S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    (h : Rounds t s rs s₁) : Rounds (deadS t) (some s) rs (some s₁) := by
  induction h with
  | nil => exact .nil _
  | cons hb _ ih => exact .cons (.inl ⟨_, _, hb, rfl⟩) ih

theorem rounds_deadS_none {σ : Option S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    (h : Rounds (deadS t) none rs σ) : σ = none := by
  cases h with
  | nil => rfl
  | cons hb _ => exact hb.elim

theorem rounds_deadS_none_cons {σ : Option S} {x : A × List (Call E) × (B ⊕ PUnit.{u + 1})}
    {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} (h : Rounds (deadS t) none (x :: rs) σ) :
    False := by
  cases h with
  | cons hb _ => exact hb.elim

theorem rounds_of_deadS {σ σ' : Option S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    (h : Rounds (deadS t) σ rs σ') : ∀ s s', σ = some s → σ' = some s' → Rounds t s rs s' := by
  induction h with
  | nil => rintro s s' rfl h; cases h; exact .nil _
  | cons hb hr ih =>
    rintro s s' rfl rfl
    rcases hb with ⟨y, s₁, h₁, he⟩ | ⟨_, _, he⟩ | ⟨_, he⟩ <;>
      simp only [End.ret.injEq, reduceCtorEq] at he
    · obtain ⟨rfl, rfl⟩ := he
      exact .cons h₁ (ih _ _ rfl rfl)
    · obtain ⟨rfl, rfl⟩ := he
      cases rounds_deadS_none hr

theorem rounds_append {X : ObsTriple E S A B} {s s₂ : S} {l₁ l₂ : List (A × List (Call E) × B)}
    (h : Rounds X s (l₁ ++ l₂) s₂) : ∃ s₁, Rounds X s l₁ s₁ ∧ Rounds X s₁ l₂ s₂ := by
  induction l₁ generalizing s with
  | nil => exact ⟨s, .nil _, h⟩
  | cons x l₁ ih =>
    cases h with
    | cons hb hr =>
      obtain ⟨s₁, h₁, h₂⟩ := ih hr
      exact ⟨s₁, .cons hb h₁, h₂⟩

theorem streamTake_succ_last {α : Type u} (ω : ℕ → α) (n : ℕ) :
    streamTake ω (n + 1) = streamTake ω n ++ [ω n] := by
  simp only [streamTake]
  rw [List.ofFn_succ_last]
  simp

/-! ## Simulations of the threading automata -/

/-- States of `threadT t` related to states of `threadT (deadS t)`. -/
inductive Fwd : TSt E S A → TSt E (Option S) A → Prop
  | idle (s : S) : Fwd (.idle s) (.idle (some s))
  | run (s : S) (a : A) (c : List (Call E)) : Fwd (.run s a c) (.run (some s) a c)
  | wait (s : S) (a : A) (c : List (Call E)) (m : E.Op) :
      Fwd (.wait s a c m) (.wait (some s) a c m)
  | dead (σ : Option S) : Fwd .dead (.idle σ)
  | stuck (a : A) (σ : Option S) : Fwd (.stuck a) (.run σ a [])

/-- States of `threadT (deadS t)` related to states of `threadT t`. -/
inductive Bwd : TSt E (Option S) A → TSt E S A → Prop
  | idle (s : S) : Bwd (.idle (some s)) (.idle s)
  | run (s : S) (a : A) (c : List (Call E)) : Bwd (.run (some s) a c) (.run s a c)
  | wait (s : S) (a : A) (c : List (Call E)) (m : E.Op) :
      Bwd (.wait (some s) a c m) (.wait s a c m)
  | dead : Bwd (.idle none) .dead
  | stuck (a : A) (c : List (Call E)) : Bwd (.run none a c) (.stuck a)

theorem fwd_step {x y : TSt E S A} {x' : TSt E (Option S) A}
    {o : Move E (sig1 A (B ⊕ PUnit.{u + 1}))} (h : TStep t.1 (satP t) x o y) (hx : Fwd x x') :
    ∃ o' y', TStep (deadS t).1 (satP (deadS t)) x' o' y' ∧ relMove o' = relMove o ∧ Fwd y y' := by
  cases h with
  | ask s a => cases hx; exact ⟨_, _, .ask _ a, rfl, .run _ _ _⟩
  | call s a c m hm =>
    cases hx
    exact ⟨_, _, .call _ _ _ _ (by rw [satP_deadS_some]; exact hm), rfl, .wait _ _ _ _⟩
  | reply s a c m n => cases hx; exact ⟨_, _, .reply _ _ _ _ n, rfl, .run _ _ _⟩
  | ret s a c b s' hb =>
    cases hx
    exact ⟨_, _, .ret _ _ _ b (some s') (.inl ⟨b, s', hb, rfl⟩), rfl, .idle _⟩
  | trap s a c hb =>
    cases hx
    by_cases hs : ∃ s₁, (c, End.ret (.inr PUnit.unit) s₁) ∈ t.1 s a
    · obtain ⟨s₁, h₁⟩ := hs
      exact ⟨_, _, .ret _ _ _ (.inr PUnit.unit) (some s₁) (.inl ⟨_, s₁, h₁, rfl⟩), rfl, .dead _⟩
    · exact ⟨_, _, .ret _ _ _ (.inr PUnit.unit) none
        (.inr (.inl ⟨hb, fun s₁ h₁ => hs ⟨s₁, h₁⟩, rfl⟩)), rfl, .dead _⟩
  | deadAsk a => cases hx; exact ⟨_, _, .ask _ a, rfl, .stuck _ _⟩

theorem fwd_run {x y : TSt E S A} {x' : TSt E (Option S) A}
    {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))} (h : TRun t.1 (satP t) x p y)
    (hx : Fwd x x') : ∃ p' y', TRun (deadS t).1 (satP (deadS t)) x' p' y' ∧
      p'.map relMove = p.map relMove := by
  induction h generalizing x' with
  | nil => exact ⟨[], _, .nil _, rfl⟩
  | cons hs _ ih =>
    obtain ⟨o', y', hs', ho, hy⟩ := fwd_step hs hx
    obtain ⟨p', z', hr, hp⟩ := ih hy
    exact ⟨o' :: p', z', .cons hs' hr, by simp [ho, hp]⟩

theorem bwd_step {x' y' : TSt E (Option S) A} {x : TSt E S A}
    {o' : Move E (sig1 A (B ⊕ PUnit.{u + 1}))} (h : TStep (deadS t).1 (satP (deadS t)) x' o' y')
    (hx : Bwd x' x) :
    ∃ o y, TStep t.1 (satP t) x o y ∧ relMove o = relMove o' ∧ Bwd y' y := by
  cases h with
  | ask σ a =>
    cases hx with
    | idle s => exact ⟨_, _, .ask s a, rfl, .run _ _ _⟩
    | dead => exact ⟨_, _, .deadAsk a, rfl, .stuck _ _⟩
  | call σ a c m hm =>
    cases hx with
    | run s => exact ⟨_, _, .call s a c m (by rwa [satP_deadS_some] at hm), rfl, .wait _ _ _ _⟩
    | stuck => rw [satP_deadS_none] at hm; exact hm.elim
  | reply σ a c m n => cases hx; exact ⟨_, _, .reply _ a c m n, rfl, .run _ _ _⟩
  | ret σ a c b σ' hb =>
    cases hx with
    | run s =>
      rcases hb with ⟨y, s₁, h₁, he⟩ | ⟨h₁, -, he⟩ | ⟨_, he⟩ <;>
        simp only [End.ret.injEq, reduceCtorEq] at he
      · obtain ⟨rfl, rfl⟩ := he
        exact ⟨_, _, .ret s a c _ s₁ h₁, rfl, .idle _⟩
      · obtain ⟨rfl, rfl⟩ := he
        exact ⟨_, _, .trap s a c h₁, rfl, .dead⟩
    | stuck => exact hb.elim
  | trap σ a c hb =>
    cases hx with
    | run s => rcases hb with ⟨_, _, _, he⟩ | ⟨_, _, he⟩ | ⟨_, he⟩ <;> cases he
    | stuck => exact hb.elim
  | deadAsk a => cases hx

theorem bwd_run {x' y' : TSt E (Option S) A} {x : TSt E S A}
    {p' : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    (h : TRun (deadS t).1 (satP (deadS t)) x' p' y')
    (hx : Bwd x' x) : ∃ p y, TRun t.1 (satP t) x p y ∧ p.map relMove = p'.map relMove := by
  induction h generalizing x with
  | nil => exact ⟨[], _, .nil _, rfl⟩
  | cons hs _ ih =>
    obtain ⟨o, y, hs', ho, hy⟩ := bwd_step hs hx
    obtain ⟨p, z, hr, hp⟩ := ih hy
    exact ⟨o :: p, z, .cons hs' hr, by simp [ho, hp]⟩

/-! ## The session -/

theorem mem_plays_deadS {s₀ : S} {q : List (Move E (sig1 A B))} :
    q ∈ (threadS (deadS t) (some s₀)).toStrategy ↔ q ∈ (threadS t s₀).toStrategy := by
  constructor
  · rintro ⟨p, ⟨y, hp⟩, rfl⟩
    obtain ⟨p', y', hp', he⟩ := bwd_run hp (.idle s₀)
    exact ⟨p', ⟨y', hp'⟩, he⟩
  · rintro ⟨p, ⟨y, hp⟩, rfl⟩
    obtain ⟨p', y', hp', he⟩ := fwd_run hp (.idle s₀)
    exact ⟨p', ⟨y', hp'⟩, he⟩

theorem mem_div_deadS {s₀ : S} {q : List (Move E (sig1 A B))} :
    q ∈ (threadS (deadS t) (some s₀)).div ↔ q ∈ (threadS t s₀).div := by
  rw [StratSession.mem_div_iff, StratSession.mem_div_iff]
  constructor
  · rintro ⟨rs, (_ | s), a, c, hr, hd, rfl⟩
    · exact hd.elim
    · rcases hd with ⟨_, _, _, he⟩ | ⟨_, _, he⟩ | ⟨hd, -⟩
      · cases he
      · cases he
      · exact ⟨rs, s, a, c, rounds_of_deadS hr _ _ rfl rfl, hd, rfl⟩
  · rintro ⟨rs, s, a, c, hr, hd, rfl⟩
    exact ⟨rs, some s, a, c, rounds_deadS hr, .inr (.inr ⟨hd, rfl⟩), rfl⟩

theorem mem_inf_deadS {s₀ : S} {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadS (deadS t) (some s₀)).inf ↔ I ∈ (threadS t s₀).inf := by
  rw [StratSession.mem_inf_iff, StratSession.mem_inf_iff]
  constructor
  · rintro (⟨rs, (_ | s), a, ω, hr, hω, rfl⟩ | ⟨a, r, rfl, hk⟩)
    · exact hω.elim
    · exact .inl ⟨rs, s, a, ω, rounds_of_deadS hr _ _ rfl rfl, hω, rfl⟩
    · refine .inr ⟨a, r, rfl, fun k => ?_⟩
      obtain ⟨σ, h⟩ := hk (k + 1)
      rw [streamTake_succ_last] at h
      obtain ⟨σ₁, h₁, h₂⟩ := rounds_append h
      rcases σ₁ with _ | s₁
      · exact (rounds_deadS_none_cons h₂).elim
      · exact ⟨s₁, rounds_of_deadS h₁ _ _ rfl rfl⟩
  · rintro (⟨rs, s, a, ω, hr, hω, rfl⟩ | ⟨a, r, rfl, hk⟩)
    · exact .inl ⟨rs, some s, a, ω, rounds_deadS hr, hω, rfl⟩
    · exact .inr ⟨a, r, rfl, fun k => let ⟨s, h⟩ := hk k; ⟨some s, rounds_deadS h⟩⟩

theorem threadS_deadS (s₀ : S) : threadS (deadS t) (some s₀) = threadS t s₀ :=
  DStrategy.ext (SetLike.ext fun _ => mem_plays_deadS) (Set.ext fun _ => mem_div_deadS)
    (Set.ext fun _ => mem_inf_deadS)

end Silmaril.Proofs.Games.Abstract.SessionLinkDead
