module

public import Silmaril.Games.Abstract.SessionRoute.Defs
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Proofs.Games.Abstract.SessionRoute.Limits

/-!
# The session of a one-call handler (proofs)

`threadS_callS`: the session of `callS g f` is the strategy of `callH g f`. The threading
automaton of `callS g f` runs each round as ask `a`, call `g a`, answer `n`, return `f a n`; the
handler's transition system runs the same round, through the configurations `callH g f a` and
`pure (f a n)`. The relation `Rel` matches the automaton states with the handler states; it is a
simulation in both directions (`fwd_run`, `bwd_run`), the backward direction lifting the answers
along `unrel`. Neither side diverges, and both have every limit of their plays: the handler by
`ofHandler_eq_limits`, the session because every play completes whole rounds up to its last
three moves (`cut`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionRoute

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionRoute

universe u

variable {E : Sig.{u}} {A B : Type u} {g : A → E.Op} {f : (a : A) → E.Ar (g a) → B ⊕ PUnit.{u + 1}}

/-- Lift a move of the handler to the threading interface: an answer is a returned answer. -/
def unrel : Move E (sig1 A B) → Move E (sig1 A (B ⊕ PUnit.{u + 1}))
  | .inl e => .inl e
  | .inr (.ask a) => .inr (.ask a)
  | .inr (.ans a x) => .inr (.ans a (.inl x))

theorem relMove_unrel (o : Move E (sig1 A B)) : relMove (unrel o) = o := by
  rcases o with e | (a | ⟨a, x⟩) <;> rfl

theorem map_relMove_unrel (q : List (Move E (sig1 A B))) : (q.map unrel).map relMove = q := by
  simp [Function.comp_def, relMove_unrel]

theorem mem_satP_callS {s : PUnit.{u + 1}} {a : A} {x : List (Call E) × E.Op} :
    x ∈ satP (callS g f) s a → x = ([], g a) := by
  rintro (h | ⟨d, m', h, n, c', hd⟩ | ⟨d, e, ⟨y, h⟩, n, c', hd⟩ | ⟨ω, h, _⟩)
  · exact h
  · simp only [callS, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp at hd
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases x with ⟨_ | ⟨z, x⟩, m⟩
    · simp only [List.nil_append, List.cons.injEq, Sigma.mk.injEq] at hd
      obtain ⟨⟨rfl, -⟩, -⟩ := hd
      rfl
    · simp at hd
  · exact h.elim

theorem self_mem_satP_callS (s : PUnit.{u + 1}) (a : A) :
    (([] : List (Call E)), g a) ∈ satP (callS g f) s a :=
  Or.inl rfl

/-- The automaton states matched with the handler states. -/
inductive Rel (g : A → E.Op) (f : (a : A) → E.Ar (g a) → B ⊕ PUnit.{u + 1}) :
    TSt E PUnit.{u + 1} A → (callH g f).toReduction.toLTS.State → Prop
  | idle (s : PUnit.{u + 1}) : Rel g f (.idle s) .idle
  | run₀ (s : PUnit.{u + 1}) (a : A) : Rel g f (.run s a []) (.run a (callH g f a))
  | wait₀ (s : PUnit.{u + 1}) (a : A) :
      Rel g f (.wait s a [] (g a)) (.wait a (g a) fun n => .pure (f a n))
  | run₁ (s : PUnit.{u + 1}) (a : A) (n : E.Ar (g a)) :
      Rel g f (.run s a [⟨g a, n⟩]) (.run a (.pure (f a n)))

theorem fwd_step {x y : TSt E PUnit.{u + 1} A} {o : Move E (sig1 A (B ⊕ PUnit.{u + 1}))}
    {z : (callH g f).toReduction.toLTS.State} (h : TStep (callS g f).1 (satP (callS g f)) x o y)
    (hr : Rel g f x z) :
    ∃ z', (callH g f).toReduction.toLTS.step z (some (relMove o)) z' ∧ Rel g f y z' := by
  cases hr with
  | idle s =>
    cases h with
    | ask s a => exact ⟨_, Reduction.Step.ask (R := (callH g f).toReduction) a, .run₀ s a⟩
  | run₀ s a =>
    cases h with
    | call s a c m hm =>
      obtain ⟨-, rfl⟩ := Prod.ext_iff.1 (mem_satP_callS hm)
      exact ⟨_, Reduction.Step.call (R := (callH g f).toReduction)
        (k := fun n => Prog.pure (f a n)) rfl, .wait₀ s a⟩
    | ret s a c b s' hb =>
      obtain ⟨n, hn⟩ := hb
      cases (Prod.ext_iff.1 hn).1
    | trap s a c hc =>
      obtain ⟨n, hn⟩ := hc
      cases (Prod.ext_iff.1 hn).2
  | wait₀ s a =>
    cases h with
    | reply s a c m n =>
      exact ⟨_, Reduction.Step.resume (R := (callH g f).toReduction) a (g a) _ n, .run₁ s a n⟩
  | run₁ s a n =>
    cases h with
    | call s a c m hm =>
      cases (Prod.ext_iff.1 (mem_satP_callS hm)).1
    | ret s a c b s' hb =>
      obtain ⟨n', hn⟩ := hb
      simp only [Prod.mk.injEq, List.cons.injEq, Sigma.mk.injEq, heq_eq_eq, true_and,
        and_true, End.ret.injEq] at hn
      obtain ⟨rfl, rfl, -⟩ := hn
      exact ⟨_, Reduction.Step.ret (R := (callH g f).toReduction) (r := f a n) rfl, .idle s'⟩
    | trap s a c hc =>
      obtain ⟨n', hn⟩ := hc
      cases (Prod.ext_iff.1 hn).2

theorem fwd_run {x y : TSt E PUnit.{u + 1} A} {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    {z : (callH g f).toReduction.toLTS.State} (h : TRun (callS g f).1 (satP (callS g f)) x p y)
    (hr : Rel g f x z) : ∃ z', (callH g f).toReduction.toLTS.Run z (p.map relMove) z' := by
  induction h generalizing z with
  | nil => exact ⟨z, .nil z⟩
  | cons hs _ ih =>
    obtain ⟨z₁, hz₁, hr₁⟩ := fwd_step hs hr
    obtain ⟨z', hz'⟩ := ih hr₁
    exact ⟨z', .vis hz₁ hz'⟩

theorem bwd_step {x : TSt E PUnit.{u + 1} A} {o : Move E (sig1 A B)}
    {z z' : (callH g f).toReduction.toLTS.State}
    (h : (callH g f).toReduction.toLTS.step z (some o) z') (hr : Rel g f x z) :
    ∃ y, TStep (callS g f).1 (satP (callS g f)) x (unrel o) y ∧ Rel g f y z' := by
  cases hr with
  | idle s =>
    cases h with
    | ask a => exact ⟨_, .ask s a, .run₀ s a⟩
  | run₀ s a =>
    cases h with
    | call hc =>
      cases hc
      exact ⟨_, .call s a [] (g a) (self_mem_satP_callS s a), .wait₀ s a⟩
    | ret hd => cases hd
  | wait₀ s a =>
    cases h with
    | resume _ _ _ n => exact ⟨_, .reply s a [] (g a) n, .run₁ s a n⟩
  | run₁ s a n =>
    cases h with
    | call hc => cases hc
    | ret hd =>
      cases hd
      exact ⟨_, .ret s a _ (f a n) PUnit.unit ⟨n, rfl⟩, .idle _⟩

theorem bwd_run {x : TSt E PUnit.{u + 1} A} {q : List (Move E (sig1 A B))}
    {z z' : (callH g f).toReduction.toLTS.State}
    (h : (callH g f).toReduction.toLTS.Run z q z') (hr : Rel g f x z) :
    ∃ y, TRun (callS g f).1 (satP (callS g f)) x (q.map unrel) y := by
  induction h generalizing x with
  | nil => exact ⟨x, .nil x⟩
  | tau hs _ _ => exact (not_silent hs).elim
  | vis hs _ ih =>
    obtain ⟨y₁, hy₁, hr₁⟩ := bwd_step hs hr
    obtain ⟨y, hy⟩ := ih hr₁
    exact ⟨y, .cons hy₁ hy⟩

/-- **The finite plays**: the session of `callS g f` has the plays of `callH g f`. -/
theorem toStrategy_threadS_callS :
    (threadS (callS g f) PUnit.unit).toStrategy = Strategy.ofHandler (callH g f) := by
  refine Strategy.ext fun q => ?_
  rw [Strategy.mem_ofHandler]
  constructor
  · rintro ⟨p, ⟨y, hp⟩, rfl⟩
    exact fwd_run hp (.idle _)
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy⟩ := bwd_run hz (.idle PUnit.unit)
    exact ⟨_, ⟨y, hy⟩, map_relMove_unrel q⟩

/-- A whole round from idle: four moves back to idle. -/
theorem round_inv {s : PUnit.{u + 1}} {o₁ o₂ o₃ o₄ : Move E (sig1 A (B ⊕ PUnit.{u + 1}))}
    {rest : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))} {y : TSt E PUnit.{u + 1} A}
    (h : TRun (callS g f).1 (satP (callS g f)) (.idle s) (o₁ :: o₂ :: o₃ :: o₄ :: rest) y) :
    ∃ s', TRun (callS g f).1 (satP (callS g f)) (.idle s) [o₁, o₂, o₃, o₄] (.idle s') ∧
      TRun (callS g f).1 (satP (callS g f)) (.idle s') rest y := by
  obtain _ | ⟨h₁, h⟩ := h
  obtain _ | ⟨h₂, h⟩ := h
  obtain _ | ⟨h₃, h⟩ := h
  obtain _ | ⟨h₄, h⟩ := h
  cases h₁ with
  | ask _ a =>
    cases h₂ with
    | ret _ _ _ _ _ hb =>
      obtain ⟨n, hn⟩ := hb
      cases (Prod.ext_iff.1 hn).1
    | trap _ _ _ hc =>
      obtain ⟨n, hn⟩ := hc
      cases (Prod.ext_iff.1 hn).2
    | call _ _ _ m hm =>
      cases h₃ with
      | reply _ _ _ _ n =>
        cases h₄ with
        | call _ _ _ _ hm' =>
          cases (Prod.ext_iff.1 (mem_satP_callS hm')).1
        | trap _ _ _ hc =>
          obtain ⟨n, hn⟩ := hc
          cases (Prod.ext_iff.1 hn).2
        | ret _ _ _ b s' hb =>
          exact ⟨s', .cons (.ask _ a) <| .cons (.call _ _ _ m hm) <|
            .cons (.reply _ _ _ _ n) <| .cons (.ret _ _ _ b s' hb) (.nil _), h⟩

/-- **A play completes whole rounds up to its last three moves.** -/
theorem cut : ∀ {s : PUnit.{u + 1}} {p : List (Move E (sig1 A (B ⊕ PUnit.{u + 1})))}
    {y : TSt E PUnit.{u + 1} A}, TRun (callS g f).1 (satP (callS g f)) (.idle s) p y →
    ∃ r s', TRun (callS g f).1 (satP (callS g f)) (.idle s) r (.idle s') ∧ r <+: p ∧
      p.length ≤ r.length + 3
  | s, [], _, _ => ⟨[], s, .nil _, List.nil_prefix, by simp⟩
  | s, [_], _, _ => ⟨[], s, .nil _, List.nil_prefix, by simp⟩
  | s, [_, _], _, _ => ⟨[], s, .nil _, List.nil_prefix, by simp⟩
  | s, [_, _, _], _, _ => ⟨[], s, .nil _, List.nil_prefix, by simp⟩
  | _, o₁ :: o₂ :: o₃ :: o₄ :: rest, _, h => by
    obtain ⟨s', h₁, h₂⟩ := round_inv h
    obtain ⟨r, s'', hr, hrp, hl⟩ := cut h₂
    exact ⟨[o₁, o₂, o₃, o₄] ++ r, s'', h₁.append hr, (List.prefix_append_right_inj _).2 hrp,
      by simp; omega⟩

/-- Images of infinite traces are infinite traces. -/
theorem isInfPlay_image_map {α β : Type u} (k : α → β) {I : Set (List α)} (hI : IsInfPlay I) :
    IsInfPlay (List.map k '' I) where
  of_prefix := by
    rintro s _ ⟨t, ht, rfl⟩ hs
    refine ⟨t.take s.length, hI.of_prefix ht (List.take_prefix _ _), ?_⟩
    rw [List.map_take]
    exact (List.prefix_iff_eq_take.1 hs).symm
  total := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    rcases hI.total hs ht with h | h
    · exact .inl (h.map _)
    · exact .inr (h.map _)
  unbounded k := by
    obtain ⟨s, hs, hk⟩ := hI.unbounded k
    exact ⟨_, ⟨s, hs, rfl⟩, by simpa using hk⟩

/-- **The session of a one-call handler has no divergence and every limit of its plays.** -/
theorem threadS_callS_eq_limits :
    threadS (callS g f) PUnit.unit =
      DStrategy.limits (threadS (callS g f) PUnit.unit).toStrategy := by
  refine DStrategy.ext rfl ?_ ?_
  · refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro _ ⟨_, ⟨_, _, _, _, n, hn⟩, _⟩
    cases (Prod.ext_iff.1 hn).2
  · ext I
    constructor
    · intro h
      exact ⟨(threadS (callS g f) PUnit.unit).inf_isInf h, fun q hq =>
        (threadS (callS g f) PUnit.unit).inf_sub h hq⟩
    rintro ⟨hI, hsub⟩
    have hlift : ∀ q ∈ I, ∃ y, TRun (callS g f).1 (satP (callS g f)) (.idle PUnit.unit)
        (q.map unrel) y := by
      intro q hq
      have hq' : q ∈ (threadS (callS g f) PUnit.unit).toStrategy := hsub hq
      rw [toStrategy_threadS_callS, Strategy.mem_ofHandler] at hq'
      obtain ⟨z, hz⟩ := hq'
      exact bwd_run hz (.idle PUnit.unit)
    refine ⟨List.map unrel '' I, ⟨isInfPlay_image_map _ hI, ?_, .inr ?_⟩, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact hlift q hq
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨q', hq', hlen⟩ := hI.unbounded (q.length + 4)
      obtain ⟨y, hy⟩ := hlift q' hq'
      obtain ⟨r, s', hr, hrq, hlen'⟩ := cut hy
      have hqq : q <+: q' := by
        rcases hI.total hq hq' with h | h
        · exact h
        · have := h.length_le; omega
      simp only [List.length_map] at hlen'
      have hr' : r = (q'.take r.length).map unrel := by
        rw [List.map_take]
        exact List.prefix_iff_eq_take.1 hrq
      refine ⟨_, ⟨q'.take r.length, hI.of_prefix hq' (List.take_prefix _ _), rfl⟩, ?_,
        s', hr' ▸ hr⟩
      have : r.length ≤ q'.length := by simpa using hrq.length_le
      exact (List.prefix_of_prefix_length_le hqq (List.take_prefix _ _)
        (by simp; omega)).map _
    · rw [Set.image_image]
      simp only [map_relMove_unrel, Set.image_id']

/-- **The session of a one-call handler is the handler's strategy.** -/
theorem threadS_callS :
    threadS (callS g f) PUnit.unit = DStrategy.ofHandler (callH g f) := by
  rw [threadS_callS_eq_limits, ofHandler_eq_limits, toStrategy_threadS_callS]

end Silmaril.Proofs.Games.Abstract.SessionRoute
