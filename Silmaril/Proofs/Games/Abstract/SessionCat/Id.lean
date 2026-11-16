module

public import Silmaril.Games.Abstract.SessionCat.Defs
public import Silmaril.Games.DivComp.Defs

/-!
# Session-level category laws: the identity session (proofs)

`threadS_idS`: the session of `idS` is copycat. Its plays: the threading automaton of `idS` runs
each round as ask `a`, call `a`, answer `y`, return `y`, which relabels to the four copycat moves
of one forwarded question (`fwd`, by a motive on automaton states); conversely the run of the
copy of a list of events is built round by round (`run_double`). The answers of `idS` are never
plain traps, so a play of copycat lifts back along `unrel`. It has no divergence. Its infinite
plays are all limits of copycat plays: a limit of copycat plays completes infinitely many rounds
(`cut`), so it is an infinite play of the threading.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionCat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionCat

universe u

variable {A B : Type u}

local notation "F" => sig1 A B

/-- Lift a copycat move to the threading interface: an answer is a returned answer. -/
def unrel : Move F F → Move F (sig1 A (B ⊕ PUnit.{u + 1}))
  | .inl e => .inl e
  | .inr (.ask a) => .inr (.ask a)
  | .inr (.ans a x) => .inr (.ans a (.inl x))

theorem relMove_unrel (o : Move F F) : relMove (unrel o) = o := by
  rcases o with e | (a | ⟨a, x⟩) <;> rfl

theorem map_relMove_unrel (q : List (Move F F)) : (q.map unrel).map relMove = q := by
  simp [Function.comp_def, relMove_unrel]

theorem mem_satP_idS {s : PUnit.{u + 1}} {a : A} {x : List (Call F) × A} :
    x ∈ satP (idS (A := A) (B := B)) s a → x = ([], a) := by
  rintro (h | ⟨d, m', h, n, c', hd⟩ | ⟨d, e, ⟨y, h⟩, n, c', hd⟩ | ⟨ω, h, _⟩)
  · exact h
  · simp only [idS, Set.mem_singleton_iff, Prod.mk.injEq] at h
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

theorem self_mem_satP_idS (s : PUnit.{u + 1}) (a : A) :
    (([] : List (Call F)), a) ∈ satP (idS (A := A) (B := B)) s a :=
  Or.inl rfl

/-- The motive of the forward direction: the moves after an automaton state complete the
current round's copycat moves to a copycat play. -/
def Fwd : TSt F PUnit.{u + 1} A → List (Move F F) → Prop
  | .idle _, q => ∃ w, Ev.Alternating w ∧ q <+: Ev.double w
  | .run _ a [], q => ∃ w, Ev.Alternating w ∧ .inr (.ask a) :: q <+: Ev.double w
  | .run _ a [⟨a', y⟩], q => a' = a →
      ∃ w, Ev.Alternating w ∧ .inr (.ask a) :: .inl (.ask a) :: .inl (.ans a y) :: q <+: Ev.double w
  | .wait _ a [] m, q => m = a →
      ∃ w, Ev.Alternating w ∧ .inr (.ask a) :: .inl (.ask a) :: q <+: Ev.double w
  | _, _ => True

theorem fwd_nil (x : TSt F PUnit.{u + 1} A) : Fwd x [] := by
  match x with
  | .idle _ => exact ⟨[], .nil, List.prefix_refl _⟩
  | .run _ a [] => exact ⟨_, .ask a, by simp⟩
  | .run _ a [⟨a', y⟩] =>
    rintro rfl
    exact ⟨[.ask a', .ans a' y], .cons _ _ .nil, by simp⟩
  | .run _ _ (_ :: _ :: _) => trivial
  | .wait _ a [] m =>
    rintro rfl
    exact ⟨_, .ask m, by simp⟩
  | .wait _ _ (_ :: _) _ => trivial
  | .dead => trivial
  | .stuck _ => trivial

theorem fwd {x y : TSt F PUnit.{u + 1} A} {p : List (Move F (sig1 A (B ⊕ PUnit.{u + 1})))}
    (h : TRun idS.1 (satP idS) x p y) : Fwd x (p.map relMove) := by
  induction h with
  | nil x => exact fwd_nil x
  | cons hs _ ih =>
    cases hs with
    | ask s a => exact ih
    | call s a c m hm =>
      obtain ⟨hc, hm'⟩ := Prod.ext_iff.1 (mem_satP_idS hm)
      simp only at hc hm'
      subst hc hm'
      exact ih rfl
    | reply s a c m n =>
      rcases c with _ | ⟨z, c⟩
      · rintro rfl; exact ih rfl
      · trivial
    | ret s a c b s' hb =>
      obtain ⟨y, hy⟩ := hb
      simp only [Prod.mk.injEq, End.ret.injEq] at hy
      obtain ⟨rfl, rfl, -⟩ := hy
      rintro -
      obtain ⟨w, hw, hq⟩ := ih
      exact ⟨.ask a :: .ans a b :: w, .cons _ _ hw, by simpa [relMove, merge] using hq⟩
    | trap s a c hc =>
      obtain ⟨y, hy⟩ := hc
      cases (Prod.ext_iff.1 hy).2
    | deadAsk a => trivial

/-- The automaton runs one forwarded round from idle to idle. -/
theorem run_round (a : A) (y : B ⊕ PUnit.{u + 1}) :
    TRun idS.1 (satP idS) (.idle PUnit.unit)
      [.inr (.ask a), .inl (.ask a), .inl (.ans a y), .inr (.ans a (.inl y))]
      (.idle PUnit.unit) := by
  have h₁ : TStep idS.1 (satP idS) (.wait PUnit.unit a [] a) (.inl (.ans a y))
      (.run PUnit.unit a [⟨a, y⟩]) := by
    have := TStep.reply (f := (idS (A := A) (B := B)).1) (P := satP idS) PUnit.unit a [] a y
    simpa using this
  have h₂ : TStep idS.1 (satP idS) (.run PUnit.unit a [⟨a, y⟩]) (.inr (.ans a (.inl y)))
      (.idle PUnit.unit) :=
    .ret (f := (idS (A := A) (B := B)).1) (P := satP idS) PUnit.unit a [⟨a, y⟩] y _ ⟨y, rfl⟩
  have h₀ : TStep idS.1 (satP idS) (.run PUnit.unit a []) (.inl (.ask a))
      (.wait PUnit.unit a [] a) :=
    TStep.call (f := (idS (A := A) (B := B)).1) (P := satP idS) PUnit.unit a [] a
      (self_mem_satP_idS _ a)
  exact .cons (.ask _ a) <| .cons h₀ <| .cons h₁ <| .cons h₂ (.nil _)

/-- The automaton runs the copy of alternating events. -/
theorem run_double {w : List (Ev F)} (hw : Ev.Alternating w) :
    ∃ z, TRun idS.1 (satP idS) (.idle PUnit.unit) ((Ev.double w).map unrel) z := by
  induction hw with
  | nil => exact ⟨_, .nil _⟩
  | ask m => exact ⟨_, .cons (.ask _ m) <| .cons (.call _ _ _ _ (self_mem_satP_idS _ m)) (.nil _)⟩
  | cons m n _ ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z, ?_⟩
    have := (run_round m n).append hz
    simpa [unrel] using this

theorem mem_plays_iff {q : List (Move F F)} :
    (∃ p ∈ (threadT idS PUnit.unit).toStrategy, p.map relMove = q) ↔
      ∃ w, Ev.Alternating w ∧ q <+: Ev.double w := by
  constructor
  · rintro ⟨p, ⟨y, hp⟩, rfl⟩
    exact fwd hp
  · rintro ⟨w, hw, r, hr⟩
    obtain ⟨z, hz⟩ := run_double hw
    rw [← hr, List.map_append] at hz
    obtain ⟨y, hy, -⟩ := hz.of_append
    exact ⟨_, ⟨y, hy⟩, map_relMove_unrel q⟩

/-- A copycat prefix completes whole rounds up to its last three moves. -/
theorem cut {w : List (Ev F)} (hw : Ev.Alternating w) {q : List (Move F F)}
    (hq : q <+: Ev.double w) : ∃ r, TRun idS.1 (satP idS) (.idle PUnit.unit) (r.map unrel)
      (.idle PUnit.unit) ∧ r <+: q ∧ q.length ≤ r.length + 3 := by
  induction hw generalizing q with
  | nil => exact ⟨[], .nil _, List.nil_prefix, by have := hq.length_le; simp at this; simp [this]⟩
  | ask m => exact ⟨[], .nil _, List.nil_prefix, by have := hq.length_le; simp at this; omega⟩
  | @cons m n w _ ih =>
    by_cases hl : q.length ≤ 3
    · exact ⟨[], .nil _, List.nil_prefix, by simpa using hl⟩
    have hX : Ev.double (.ask m :: .ans m n :: w) =
        [.inr (.ask m), .inl (.ask m), .inl (.ans m n), .inr (.ans m n)] ++ Ev.double w := by
      simp
    rw [hX] at hq
    obtain ⟨q', rfl⟩ := List.prefix_of_prefix_length_le (List.prefix_append _ _) hq
      (by simp; omega)
    obtain ⟨r, hr, hrq, hlen⟩ := ih ((List.prefix_append_right_inj _).1 hq)
    refine ⟨_ ++ r, ?_, (List.prefix_append_right_inj _).2 hrq, by simp; omega⟩
    rw [List.map_append]
    exact (run_round m n).append hr

/-- Images of infinite traces are infinite traces. -/
theorem isInfPlay_image_map {α β : Type u} (f : α → β) {I : Set (List α)} (hI : IsInfPlay I) :
    IsInfPlay (List.map f '' I) where
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

theorem threadS_idS : threadS (idS (A := A) (B := B)) PUnit.unit = DStrategy.id (sig1 A B) := by
  have hp : (threadS (idS (A := A) (B := B)) PUnit.unit).toStrategy = Strategy.id (sig1 A B) :=
    Strategy.ext fun _ => mem_plays_iff
  refine DStrategy.ext hp ?_ ?_
  · refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro _ ⟨_, ⟨_, _, _, _, y, hy⟩, _⟩
    cases (Prod.ext_iff.1 hy).2
  · ext I
    constructor
    · intro h
      exact ⟨(threadS idS PUnit.unit).inf_isInf h, fun q hq =>
        hp ▸ (threadS idS PUnit.unit).inf_sub h hq⟩
    rintro ⟨hI, hsub⟩
    refine ⟨List.map unrel '' I, ⟨isInfPlay_image_map _ hI, ?_, .inr ?_⟩, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨w, hw, r, hr⟩ := hsub hq
      obtain ⟨z, hz⟩ := run_double hw
      rw [← hr, List.map_append] at hz
      obtain ⟨y, hy, -⟩ := hz.of_append
      exact ⟨y, hy⟩
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨q', hq', hlen⟩ := hI.unbounded (q.length + 4)
      obtain ⟨w, hw, hpre⟩ := hsub hq'
      obtain ⟨r, hr, hrq, hlen'⟩ := cut hw hpre
      have hqq : q <+: q' := by
        rcases hI.total hq hq' with h | h
        · exact h
        · have := h.length_le; omega
      exact ⟨_, ⟨r, hI.of_prefix hq' hrq, rfl⟩,
        (List.prefix_of_prefix_length_le hqq hrq (by omega)).map _, _, hr⟩
    · rw [Set.image_image]
      simp only [map_relMove_unrel, Set.image_id']

end Silmaril.Proofs.Games.Abstract.SessionCat
