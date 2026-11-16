module

public import Silmaril.Games.Abstract.StratSession.Defs
public import Silmaril.Games.Abstract.StratThread.Thms

/-!
# Sessions: proofs

* Relabelling moves: images of call moves, rounds and traps under `relMove`, and preimages of
  session rounds (`preimage_sroundMoves`).
* Completed session rounds (`mem_srounds`), through `StratThread.mem_append_rounds` and
  `StratThread.mem_trap`.
* Plays after completed session rounds (`preimage_append_srounds`): a preimage is a play after
  completed rounds, or a plain trap ends the rounds; hence pending calls (`mem_pending`),
  divergence (`mem_div`, `mem_div_iff`) and stream plays (`mem_inf`).
* Injectivity of the relabelling on plays without plain traps (`eq_of_relabel_eq`).
* Infinite plays: images of limits (`image_lim`), stream plays and round plays; the trace form
  (`mem_inf_iff`) and the store-deterministic form (`mem_inf_iff_of_storeDet`).
-/

public section

namespace Silmaril.Proofs.Games.Abstract.StratSession

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratThread
open Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.StratObs (callMoves satP)

universe u

variable {E : Sig.{u}} {S A B : Type u}

/-! ## Relabelling moves -/

section Moves

theorem map_callMoves (c : List (Call E)) :
    (callMoves c : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))).map relMove = callMoves c := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    simp only [callMoves, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih]; rfl

theorem map_roundMoves (r : A × List (Call E) × (B ⊕ PUnit.{u + 1})) :
    (roundMoves r).map relMove = (sroundMoves r : List (Move E (sig1 A B))) := by
  simp [roundMoves, sroundMoves, map_callMoves, relMove, merge]

theorem map_roundsMoves (rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    (roundsMoves rs).map relMove = (sroundsMoves rs : List (Move E (sig1 A B))) := by
  simp [roundsMoves, sroundsMoves, List.map_flatMap, map_roundMoves]

theorem map_trapMoves (a : A) (c : List (Call E)) :
    (trapMoves a c : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))).map relMove =
      (sroundMoves (a, c, .inr PUnit.unit) : List (Move E (sig1 A B))) := by
  simp [trapMoves, sroundMoves, map_callMoves, relMove, merge]

theorem preimage_callMoves {c : List (Call E)} {l : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    (h : l.map relMove = callMoves c) : l = callMoves c := by
  induction c generalizing l with
  | nil => simpa [callMoves] using h
  | cons x c ih =>
    rcases l with _ | ⟨o₁, _ | ⟨o₂, l⟩⟩
    · simp [callMoves] at h
    · simp [callMoves] at h
    · simp only [List.map_cons, callMoves, List.flatMap_cons, List.cons_append, List.nil_append,
        List.cons.injEq] at h
      obtain ⟨h₁, h₂, h₃⟩ := h
      have e₁ : o₁ = .inl (.ask x.1) := by
        rcases o₁ with e | (_ | ⟨_, _⟩) <;> simp_all [relMove]
      have e₂ : o₂ = .inl (.ans x.1 x.2) := by
        rcases o₂ with e | (_ | ⟨_, _⟩) <;> simp_all [relMove]
      have := ih h₃
      subst e₁ e₂
      simp only [callMoves] at this
      simp [callMoves, this]

theorem preimage_ans {a : A} {x : B ⊕ PUnit.{u + 1}} {o : Move E (sig1 A (B ⊕ PUnit.{u + 1}))}
    (h : relMove o = (.inr (.ans a x) : Move E (sig1 A B))) :
    o = .inr (.ans a (.inl x)) ∨ (x = .inr PUnit.unit ∧ o = .inr (.ans a (.inr PUnit.unit))) := by
  rcases o with e | (_ | ⟨a', y⟩)
  · simp [relMove] at h
  · simp [relMove] at h
  · simp only [relMove, Sum.inr.injEq, Ev.ans.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have h : merge y = x := eq_of_heq h
    subst h
    rcases y with y | ⟨⟩
    · exact .inl rfl
    · exact .inr ⟨rfl, rfl⟩

theorem preimage_sroundMoves {r : A × List (Call E) × (B ⊕ PUnit.{u + 1})}
    {l : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    (h : l.map relMove = (sroundMoves r : List (Move E (sig1 A B)))) :
    l = roundMoves r ∨ (r.2.2 = .inr PUnit.unit ∧ l = trapMoves r.1 r.2.1) := by
  obtain ⟨a, c, x⟩ := r
  rcases l with _ | ⟨o, l⟩
  · simp [sroundMoves] at h
  simp only [List.map_cons, sroundMoves, List.cons.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  have e₁ : o = .inr (.ask a) := by
    rcases o with e | (_ | ⟨_, _⟩) <;> simp_all [relMove]
  subst e₁
  obtain ⟨l₁, l₂, rfl, h₃, h₄⟩ := List.map_eq_append_iff.1 h₂
  obtain rfl := preimage_callMoves h₃
  rcases l₂ with _ | ⟨o, _ | ⟨_, _⟩⟩ <;> simp at h₄
  rcases preimage_ans h₄ with rfl | ⟨rfl, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨rfl, rfl⟩

theorem sroundsMoves_eq_nil {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} :
    (sroundsMoves rs : List (Move E (sig1 A B))) = [] ↔ rs = [] := by
  rcases rs with _ | ⟨r, rs⟩
  · simp [sroundsMoves]
  · simp [sroundsMoves, sroundMoves]

theorem sroundsMoves_ne_ask {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {a : A} :
    (sroundsMoves rs : List (Move E (sig1 A B))) ≠ [.inr (.ask a)] := by
  rcases rs with _ | ⟨r, rs⟩
  · simp [sroundsMoves]
  · simp [sroundsMoves, sroundMoves]

end Moves

/-! ## Completed session rounds -/

section Rounds

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

theorem mem_srounds {s₀ : S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} :
    sroundsMoves rs ∈ (threadS t s₀).toStrategy ↔ (∃ s, Rounds t s₀ rs s) ∨
      ∃ rs' a c, rs = rs' ++ [(a, c, .inr PUnit.unit)] ∧
        ∃ s, Rounds t s₀ rs' s ∧ (c, .trap) ∈ t.1 s a := by
  constructor
  · rintro ⟨p, hp, hpr⟩
    induction rs generalizing s₀ p with
    | nil => exact .inl ⟨s₀, .nil _⟩
    | cons r rs ih =>
      have hpr' : p.map relMove = sroundMoves r ++ sroundsMoves rs := by
        rw [hpr]; simp [sroundsMoves]
      obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 hpr'
      rcases preimage_sroundMoves h₁ with rfl | ⟨hx, rfl⟩
      · have hp' : roundsMoves [r] ++ l₂ ∈ (threadT t s₀).toStrategy := by
          simpa [roundsMoves] using hp
        obtain ⟨s₁, hs₁, hl₂⟩ := mem_append_rounds.1 hp'
        have hr : (r.2.1, End.ret r.2.2 s₁) ∈ t.1 s₀ r.1 := by
          cases hs₁ with | cons hr hn => cases hn; exact hr
        rcases ih _ hl₂ h₂ with ⟨s, hs⟩ | ⟨rs', a, c, rfl, s, hs, htr⟩
        · exact .inl ⟨s, .cons hr hs⟩
        · exact .inr ⟨r :: rs', a, c, rfl, s, .cons hr hs, htr⟩
      · have hp' : roundsMoves [] ++ (trapMoves r.1 r.2.1 ++ l₂) ∈ (threadT t s₀).toStrategy := by
          simpa [roundsMoves] using hp
        obtain ⟨⟨s, hs, htr⟩, hl⟩ := mem_trap.1 hp'
        cases hs
        rcases hl with rfl | ⟨a', rfl⟩
        · obtain rfl := sroundsMoves_eq_nil.1 (by simpa using h₂.symm)
          obtain ⟨a, c, x⟩ := r
          simp only at hx htr
          subst hx
          exact .inr ⟨[], a, c, rfl, s₀, .nil _, htr⟩
        · exact absurd (by simpa [relMove] using h₂.symm) sroundsMoves_ne_ask
  · rintro (⟨s, hs⟩ | ⟨rs', a, c, rfl, s, hs, htr⟩)
    · exact ⟨_, mem_rounds.2 ⟨s, hs⟩, map_roundsMoves rs⟩
    · refine ⟨roundsMoves rs' ++ (trapMoves a c ++ []),
        mem_trap.2 ⟨⟨s, hs, htr⟩, .inl rfl⟩, ?_⟩
      simp [map_roundsMoves, map_trapMoves, sroundsMoves]

theorem mem_srounds_snoc_ret {s₀ : S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    {a : A} {c : List (Call E)} {b : B} :
    sroundsMoves (rs ++ [(a, c, .inl b)]) ∈ (threadS t s₀).toStrategy ↔
      ∃ s, Rounds t s₀ (rs ++ [(a, c, .inl b)]) s := by
  rw [mem_srounds]
  refine or_iff_left ?_
  rintro ⟨rs', a', c', h, -⟩
  have := congrArg List.getLast? h
  simp at this

theorem mem_trap_ret {s₀ : S} {a a' : A} {c₁ c₂ : List (Call E)} {b : B} :
    sroundMoves (a, c₁, .inr PUnit.unit) ++ sroundMoves (a', c₂, .inl b) ∈
        (threadS t s₀).toStrategy ↔
      ∃ s₁, (c₁, .ret (.inr PUnit.unit) s₁) ∈ t.1 s₀ a ∧ ∃ s₂, (c₂, .ret (.inl b) s₂) ∈ t.1 s₁ a' := by
  have h := mem_srounds_snoc_ret (t := t) (s₀ := s₀) (rs := [(a, c₁, .inr PUnit.unit)]) (a := a')
    (c := c₂) (b := b)
  simp only [sroundsMoves, List.cons_append, List.nil_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil] at h
  rw [h]
  constructor
  · rintro ⟨s, h⟩
    cases h with
    | cons h₁ h =>
      cases h with
      | cons h₂ h => cases h; exact ⟨_, h₁, _, h₂⟩
  · rintro ⟨s₁, h₁, s₂, h₂⟩
    exact ⟨s₂, .cons h₁ (.cons h₂ (.nil _))⟩

end Rounds

/-! ## Plays after completed session rounds -/

section After

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}

theorem preimage_ask_calls {a : A} {c : List (Call E)} {w : List (Move E (sig1 A B))}
    {l : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    (h : l.map relMove = .inr (.ask a) :: (callMoves c ++ w)) :
    ∃ l', l = .inr (.ask a) :: (callMoves c ++ l') ∧ l'.map relMove = w := by
  rcases l with _ | ⟨o, l⟩
  · simp at h
  simp only [List.map_cons, List.cons.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  have e₁ : o = .inr (.ask a) := by
    rcases o with e | (_ | ⟨_, _⟩) <;> simp_all [relMove]
  subst e₁
  obtain ⟨l₁, l₂, rfl, h₃, h₄⟩ := List.map_eq_append_iff.1 h₂
  obtain rfl := preimage_callMoves h₃
  exact ⟨l₂, rfl, h₄⟩

/-- A preimage of a play after completed session rounds is a play after the completed rounds of
the store-retaining triple, or the session rounds end with a plain trap and at most a question
follows. -/
theorem preimage_append_srounds {s₀ : S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    {q : List (Move E (sig1 A B))} {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    (hp : p ∈ (threadT t s₀).toStrategy) (he : p.map relMove = sroundsMoves rs ++ q) :
    (∃ s p', Rounds t s₀ rs s ∧ p = roundsMoves rs ++ p' ∧ p' ∈ (threadT t s).toStrategy ∧
      p'.map relMove = q) ∨
    ∃ rs' a c, rs = rs' ++ [(a, c, .inr PUnit.unit)] ∧ ∃ w, p = roundsMoves rs' ++ (trapMoves a c ++ w) ∧
      w.map relMove = q ∧ (w = [] ∨ ∃ a', w = [.inr (.ask a')]) := by
  induction rs generalizing s₀ p with
  | nil => exact .inl ⟨s₀, p, .nil _, by simp [roundsMoves], hp, by simpa [sroundsMoves] using he⟩
  | cons r rs ih =>
    have he' : p.map relMove = sroundMoves r ++ (sroundsMoves rs ++ q) := by
      rw [he]; simp [sroundsMoves]
    obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 he'
    rcases preimage_sroundMoves h₁ with rfl | ⟨hx, rfl⟩
    · have hp' : roundsMoves [r] ++ l₂ ∈ (threadT t s₀).toStrategy := by
        simpa [roundsMoves] using hp
      obtain ⟨s₁, hs₁, hl₂⟩ := mem_append_rounds.1 hp'
      have hr : (r.2.1, End.ret r.2.2 s₁) ∈ t.1 s₀ r.1 := by
        cases hs₁ with | cons hr hn => cases hn; exact hr
      rcases ih hl₂ h₂ with ⟨s, p', hs, rfl, hp'', hq⟩ | ⟨rs', a, c, rfl, w, rfl, hw, hw'⟩
      · exact .inl ⟨s, p', .cons hr hs, by simp [roundsMoves], hp'', hq⟩
      · exact .inr ⟨r :: rs', a, c, rfl, w, by simp [roundsMoves], hw, hw'⟩
    · have hp' : roundsMoves [] ++ (trapMoves r.1 r.2.1 ++ l₂) ∈ (threadT t s₀).toStrategy := by
        simpa [roundsMoves] using hp
      obtain ⟨-, hl⟩ := mem_trap.1 hp'
      rcases rs with _ | ⟨r', rs⟩
      · obtain ⟨a, c, x⟩ := r
        simp only at hx
        subst hx
        exact .inr ⟨[], a, c, rfl, l₂, by simp [roundsMoves], by simpa [sroundsMoves] using h₂, hl⟩
      · exfalso
        rcases hl with rfl | ⟨a', rfl⟩ <;> simp [sroundsMoves, sroundMoves, relMove] at h₂

theorem mem_pending {s₀ : S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {a : A}
    {c : List (Call E)} {m : E.Op} :
    sroundsMoves rs ++ .inr (.ask a) :: (callMoves c ++ [.inl (.ask m)]) ∈
      (threadS t s₀).toStrategy ↔ ∃ s, Rounds t s₀ rs s ∧ (c, m) ∈ satP t s a := by
  constructor
  · rintro ⟨p, hp, he⟩
    rcases preimage_append_srounds hp he with ⟨s, p', hs, rfl, hp', hq⟩ | ⟨-, -, -, -, w, -, hw, hw'⟩
    · obtain ⟨l', rfl, hl'⟩ := preimage_ask_calls hq
      obtain ⟨o, rfl⟩ : ∃ o, l' = [o] := by
        rcases l' with _ | ⟨o, _ | _⟩ <;> simp at hl' ⊢
      have ho : o = .inl (.ask m) := by
        rcases o with e | (_ | ⟨_, _⟩) <;> simp_all [relMove]
      subst ho
      obtain ⟨s', hs', hP⟩ := (StratThread.mem_pending (t := t) (s₀ := s) (rs := [])).1
        (by simpa [roundsMoves] using hp')
      cases hs'
      exact ⟨s, hs, hP⟩
    · exfalso
      rcases hw' with rfl | ⟨a', rfl⟩ <;> simp [relMove] at hw
  · rintro ⟨s, hs, hP⟩
    exact ⟨_, StratThread.mem_pending.2 ⟨s, hs, hP⟩,
      by simp [map_roundsMoves, map_callMoves, relMove]⟩

theorem mem_div {s₀ : S} {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {a : A}
    {c : List (Call E)} :
    sroundsMoves rs ++ .inr (.ask a) :: callMoves c ∈ (threadS t s₀).div ↔
      ∃ s, Rounds t s₀ rs s ∧ (c, .div) ∈ t.1 s a := by
  constructor
  · rintro ⟨p, hp, he⟩
    rcases preimage_append_srounds ((threadT t s₀).div_mem hp) he with
      ⟨s, p', -, rfl, -, hq⟩ | ⟨rs', a', c', -, w, rfl, hw, hw'⟩
    · obtain ⟨l', rfl, hl'⟩ := preimage_ask_calls (w := []) (by simpa using hq)
      obtain rfl : l' = [] := by simpa using hl'
      exact StratThread.mem_div.1 (by simpa using hp)
    · exfalso
      rcases hw' with rfl | ⟨a'', rfl⟩
      · simp at hw
      · obtain ⟨s, a₁, c₁, h, -⟩ := hp
        rw [show roundsMoves rs' ++ (trapMoves a' c' ++ [.inr (.ask a'')]) =
            (roundsMoves rs' ++ .inr (.ask a') :: callMoves c') ++
              [.inr (.ans a' (.inr PUnit.unit))] ++ [.inr (.ask a'')] by simp [trapMoves]] at h
        obtain ⟨y, h₁, h₂⟩ := h.of_append
        obtain ⟨z, -, h₃⟩ := h₁.of_append
        cases h₂ with
        | cons h₄ h₅ =>
          cases h₅
          cases h₄
          cases h₃ with
          | cons h₆ h₇ => cases h₇; cases h₆
  · rintro ⟨s, hs, hd⟩
    exact ⟨_, StratThread.mem_div.2 ⟨s, hs, hd⟩, by simp [map_roundsMoves, map_callMoves, relMove]⟩

theorem mem_div_iff {s₀ : S} {p : List (Move E (sig1 A B))} :
    p ∈ (threadS t s₀).div ↔ ∃ rs s a c, Rounds t s₀ rs s ∧ (c, .div) ∈ t.1 s a ∧
      p = sroundsMoves rs ++ .inr (.ask a) :: callMoves c := by
  constructor
  · rintro ⟨p', hp', rfl⟩
    obtain ⟨rs, s, a, c, hrs, hd, rfl⟩ := StratThread.mem_div_iff.1 hp'
    exact ⟨rs, s, a, c, hrs, hd, by simp [map_roundsMoves, map_callMoves, relMove]⟩
  · rintro ⟨rs, s, a, c, hrs, hd, rfl⟩
    exact mem_div.2 ⟨s, hrs, hd⟩

end After

/-! ## Injectivity on plays without plain traps -/

section Inj

/-- A plain trap answer. -/
def IsPlainTrap : Move E (sig1 A (B ⊕ PUnit.{u + 1})) → Prop
  | .inr (.ans _ (.inr _)) => True
  | _ => False

/-- A play with no plain trap answer. -/
def Clean (p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))) : Prop := ∀ o ∈ p, ¬ IsPlainTrap o

theorem relMove_inj {o o' : Move E (sig1 A (B ⊕ PUnit.{u + 1}))} (ho : ¬ IsPlainTrap o)
    (ho' : ¬ IsPlainTrap o') (h : relMove o = relMove o') : o = o' := by
  rcases o with e | (a | ⟨a, x⟩) <;> rcases o' with e' | (a' | ⟨a', x'⟩) <;>
    simp only [relMove, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Ev.ask.injEq,
      Ev.ans.injEq] at h
  · rw [h]
  · rw [h]
  · obtain ⟨rfl, h⟩ := h
    rcases x with x | ⟨⟩ <;> rcases x' with x' | ⟨⟩ <;> simp_all [IsPlainTrap, merge]

theorem map_inj {p p' : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))} (hp : Clean p)
    (hp' : Clean p') (h : p.map relMove = p'.map relMove) : p = p' := by
  induction p generalizing p' with
  | nil => simpa using h.symm
  | cons o p ih =>
    rcases p' with _ | ⟨o', p'⟩
    · simp at h
    · simp only [List.map_cons, List.cons.injEq] at h
      rw [relMove_inj (hp o (by simp)) (hp' o' (by simp)) h.1,
        ih (fun x hx => hp x (by simp [hx])) (fun x hx => hp' x (by simp [hx])) h.2]

theorem clean_of_run {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} (ht : NoPlainTrap t)
    {x y : TSt E S A} {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    (h : TRun t.1 (satP t) x p y) : Clean p := by
  induction h with
  | nil => simp [Clean]
  | cons hs _ ih =>
    intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · cases hs with
      | trap _ _ _ hr => exact absurd hr (ht _ _ _)
      | _ => simp [IsPlainTrap]
    · exact ih o ho

theorem eq_of_relabel_eq {σ τ : DStrategy E (sig1 A (B ⊕ PUnit.{u + 1}))}
    (hσ : ∀ p ∈ σ.toStrategy, Clean p) (hτ : ∀ p ∈ τ.toStrategy, Clean p)
    (h : relabel σ = relabel τ) : σ = τ := by
  have hp : ∀ {σ τ : DStrategy E (sig1 A (B ⊕ PUnit.{u + 1}))},
      (∀ p ∈ σ.toStrategy, Clean p) → (∀ p ∈ τ.toStrategy, Clean p) → relabel σ = relabel τ →
        σ.toStrategy.plays ⊆ τ.toStrategy.plays := by
    intro σ τ hσ hτ h p hp
    have : p.map relMove ∈ (relabel τ).toStrategy.plays := h ▸ ⟨p, hp, rfl⟩
    obtain ⟨p', hp', he⟩ := this
    rwa [← map_inj (hτ p' hp') (hσ p hp) he]
  have hd : ∀ {σ τ : DStrategy E (sig1 A (B ⊕ PUnit.{u + 1}))},
      (∀ p ∈ σ.toStrategy, Clean p) → (∀ p ∈ τ.toStrategy, Clean p) → relabel σ = relabel τ →
        σ.div ⊆ τ.div := by
    intro σ τ hσ hτ h p hp
    have : p.map relMove ∈ (relabel τ).div := h ▸ ⟨p, hp, rfl⟩
    obtain ⟨p', hp', he⟩ := this
    rwa [← map_inj (hτ p' (τ.div_mem hp')) (hσ p (σ.div_mem hp)) he]
  have hi : ∀ {σ τ : DStrategy E (sig1 A (B ⊕ PUnit.{u + 1}))},
      (∀ p ∈ σ.toStrategy, Clean p) → (∀ p ∈ τ.toStrategy, Clean p) → relabel σ = relabel τ →
        σ.inf ⊆ τ.inf := by
    intro σ τ hσ hτ h I hI
    have : List.map relMove '' I ∈ (relabel τ).inf := h ▸ ⟨I, hI, rfl⟩
    obtain ⟨I', hI', he⟩ := this
    have hsub : ∀ {I I' : Set (List (Move E (sig1 A (B ⊕ PUnit.{u + 1}))))},
        (∀ p ∈ I, Clean p) → (∀ p ∈ I', Clean p) → List.map relMove '' I = List.map relMove '' I' →
          I ⊆ I' := by
      intro I I' hc hc' he p hp
      obtain ⟨p', hp', hpe⟩ : p.map relMove ∈ List.map relMove '' I' := he ▸ ⟨p, hp, rfl⟩
      rwa [← map_inj (hc' p' hp') (hc p hp) hpe]
    have hc : ∀ p ∈ I, Clean p := fun p hp => hσ p (σ.inf_sub hI hp)
    have hc' : ∀ p ∈ I', Clean p := fun p hp => hτ p (τ.inf_sub hI' hp)
    rwa [(hsub hc hc' he).antisymm (hsub hc' hc he.symm)]
  exact DStrategy.ext (Strategy.ext fun p => ⟨fun h' => hp hσ hτ h h', fun h' => hp hτ hσ h.symm h'⟩)
    ((hd hσ hτ h).antisymm (hd hτ hσ h.symm)) ((hi hσ hτ h).antisymm (hi hτ hσ h.symm))

theorem threadT_eq_of_threadS_eq {S' : Type u} {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})}
    {t' : ObsTriple E S' A (B ⊕ PUnit.{u + 1})} (ht : NoPlainTrap t) (ht' : NoPlainTrap t')
    {s : S} {s' : S'} (h : threadS t s = threadS t' s') : threadT t s = threadT t' s' :=
  eq_of_relabel_eq (fun _ ⟨_, hp⟩ => clean_of_run ht hp) (fun _ ⟨_, hp⟩ => clean_of_run ht' hp) h

end Inj

/-! ## Infinite plays -/

section Inf

theorem image_lim {α β : Type u} (f : α → β) (c : Chain α) :
    List.map f '' Chain.lim c = Chain.lim fun n => (c n).map f := by
  ext q
  constructor
  · rintro ⟨p, ⟨n, hp⟩, rfl⟩
    exact ⟨n, hp.map f⟩
  · rintro ⟨n, hq⟩
    refine ⟨(c n).take q.length, ⟨n, List.take_prefix _ _⟩, ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hq).symm

theorem image_streamPlay (pre : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))) (a : A)
    (ω : ℕ → Call E) :
    List.map relMove '' streamPlay pre a ω = streamPlay (pre.map relMove) a ω := by
  have := image_lim (relMove (E := E) (A := A) (B := B))
    (fun k => pre ++ .inr (.ask a) :: callMoves (streamTake ω k))
  simp only [List.map_append, List.map_cons, map_callMoves] at this
  exact this

theorem image_roundsPlay (a : ℕ → A) (r : ℕ → List (Call E) × (B ⊕ PUnit.{u + 1})) :
    List.map relMove '' roundsPlay a r = (sroundsPlay a r : Set (List (Move E (sig1 A B)))) := by
  rw [roundsPlay, image_lim]
  simp only [map_roundsMoves]
  rfl

variable {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}

theorem mem_inf_iff_of_storeDet (ht : StoreDet t) {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadS t s₀).inf ↔
      (∃ rs s a ω, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a ∧ I = streamPlay (sroundsMoves rs) a ω) ∨
      ∃ a r s, InfRounds t s₀ a r s ∧ I = sroundsPlay a r := by
  constructor
  · rintro ⟨J, hJ, rfl⟩
    rcases (StratThread.mem_inf_iff_of_storeDet ht).1 hJ with
      ⟨pre, s, a, ω, hpre, hω, rfl⟩ | ⟨a, r, s, hr, rfl⟩
    · obtain ⟨rs, rfl, hrs⟩ := run_idle_iff.1 hpre
      exact .inl ⟨rs, s, a, ω, hrs, hω, by rw [image_streamPlay, map_roundsMoves]⟩
    · exact .inr ⟨a, r, s, hr, image_roundsPlay a r⟩
  · rintro (⟨rs, s, a, ω, hrs, hω, rfl⟩ | ⟨a, r, s, hr, rfl⟩)
    · exact ⟨_, streamPlay_mem (run_idle_iff.2 ⟨rs, rfl, hrs⟩) hω,
        by rw [image_streamPlay, map_roundsMoves]⟩
    · exact ⟨_, hr.mem_inf, (image_roundsPlay a r).symm⟩

theorem mem_inf_iff {I : Set (List (Move E (sig1 A B)))} :
    I ∈ (threadS t s₀).inf ↔
      (∃ rs s a ω, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a ∧ I = streamPlay (sroundsMoves rs) a ω) ∨
      ∃ a r, I = sroundsPlay a r ∧ ∀ k, ∃ s, Rounds t s₀ (streamTake (fun i => (a i, r i)) k) s := by
  constructor
  · rintro ⟨J, hJ, rfl⟩
    rcases StratThread.mem_inf_iff.1 hJ with ⟨pre, s, a, ω, hpre, hω, rfl⟩ | ⟨a, r, rfl, hr⟩
    · obtain ⟨rs, rfl, hrs⟩ := run_idle_iff.1 hpre
      exact .inl ⟨rs, s, a, ω, hrs, hω, by rw [image_streamPlay, map_roundsMoves]⟩
    · exact .inr ⟨a, r, image_roundsPlay a r, hr⟩
  · rintro (⟨rs, s, a, ω, hrs, hω, rfl⟩ | ⟨a, r, rfl, hr⟩)
    · exact ⟨_, streamPlay_mem (run_idle_iff.2 ⟨rs, rfl, hrs⟩) hω,
        by rw [image_streamPlay, map_roundsMoves]⟩
    · exact ⟨_, roundsPlay_mem hr, (image_roundsPlay a r).symm⟩

theorem length_callMoves {F : Sig.{u}} (c : List (Call E)) :
    (callMoves c : List (Move E F)).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    simp only [callMoves, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]; simp; omega

theorem streamTake_prefix_succ {α : Type u} (ω : ℕ → α) (k : ℕ) :
    streamTake ω k <+: streamTake ω (k + 1) := by
  have h : streamTake ω k = (streamTake ω (k + 1)).take k :=
    List.ext_getElem (by simp [streamTake]) fun i h₁ h₂ => by
      simp only [streamTake, List.getElem_take, List.getElem_ofFn]
  rw [h]
  exact List.take_prefix _ _

theorem mem_inf {rs : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))} {a : A}
    {ω : ℕ → Call E} :
    streamPlay (sroundsMoves rs) a ω ∈ (threadS t s₀).inf ↔
      ∃ s, Rounds t s₀ rs s ∧ ω ∈ t.2.2 s a := by
  constructor
  · rintro ⟨J, hJ, hJe⟩
    have hJI := (threadT t s₀).inf_isInf hJ
    have hX : ∀ k, roundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω (k + 1)) ∈ J := by
      intro k
      have hm : sroundsMoves rs ++ .inr (.ask a) :: callMoves (streamTake ω (k + 1)) ∈
          List.map relMove '' J := by
        rw [← hJe]; exact ⟨k + 1, List.prefix_refl _⟩
      obtain ⟨p, hp, he⟩ := hm
      rcases preimage_append_srounds ((threadT t s₀).inf_sub hJ hp) he with
        ⟨s, p', -, rfl, -, hq⟩ | ⟨-, -, -, -, w, -, hw, hw'⟩
      · obtain ⟨l', rfl, hl'⟩ := preimage_ask_calls (w := []) (by simpa using hq)
        obtain rfl : l' = [] := by simpa using hl'
        simpa using hp
      · exfalso
        rcases hw' with rfl | ⟨a', rfl⟩ <;>
          simp [relMove, callMoves, streamTake, List.ofFn_succ] at hw
    have hlen : ∀ k, (roundsMoves rs ++ .inr (.ask a) ::
        callMoves (streamTake ω k) : List (Move E (sig1 A (B ⊕ PUnit)))).length =
        (sroundsMoves rs ++ .inr (.ask a) ::
          callMoves (streamTake ω k) : List (Move E (sig1 A B))).length := fun k => by
      rw [← map_roundsMoves]; simp [length_callMoves]
    have hJs : J = streamPlay (roundsMoves rs) a ω := by
      ext q
      constructor
      · intro hq
        obtain ⟨k, hk⟩ : q.map relMove ∈ streamPlay (sroundsMoves rs) a ω := hJe ▸ ⟨q, hq, rfl⟩
        rcases hJI.total hq (hX k) with h | h
        · exact ⟨k + 1, h⟩
        · exfalso
          have h₁ := h.length_le
          have h₂ := hk.length_le
          have h₃ := hlen k
          simp [length_callMoves, streamTake] at h₁ h₂ h₃
          omega
      · rintro ⟨k, hk⟩
        refine hJI.of_prefix (hX k) (hk.trans ?_)
        obtain ⟨d, hd⟩ := streamTake_prefix_succ ω k
        rw [← hd]
        simp [callMoves]
    exact StratThread.mem_inf.1 (hJs ▸ hJ)
  · rintro ⟨s, hs, hω⟩
    exact ⟨_, StratThread.mem_inf.2 ⟨s, hs, hω⟩, by rw [image_streamPlay, map_roundsMoves]⟩

end Inf

end Silmaril.Proofs.Games.Abstract.StratSession
