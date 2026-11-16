module

public import Silmaril.Games.AnsPull.Defs
public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.LTS.Thms

/-!
# Relabelling answers below: interactions with the relabelling handler (proofs)

An interaction `Zip w t p` of a play `w` of `ansH k` (below) with a play `t` over
`⟨E.Op, B'⟩ ↠ G` shows a play `p` whose lower relabelling is `t`, up to the round in progress at
the handler: it may have accepted a question `q` from `t` not yet forwarded (`t` has one more
move, the call), or received an answer `n` not yet returned (`p` has one more move, the answer).
In both cases `t` ends waiting (`zip_out`, with the shape of the remaining moves for each handler
state in `Out`). Conversely the doubling `dblL p` of `p` is a play of the handler (`run_dblL`)
interacting with `p.map (lowMove k)` to show `p` (`zip_dblL`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.AnsPull

open Silmaril.Games

universe u

variable {E G : Sig.{u}} {B' : E.Op → Type u} (k : (q : E.Op) → E.Ar q → B' q)

/-- The upper play is the relabelled visible play, or adds a call the handler has not forwarded,
or lacks an answer the handler has not returned; in the last two cases it ends waiting. -/
def C0 (t : List (Move (Sig.mk E.Op B') G)) (p : List (Move E G)) (x' : Pos (Sig.mk E.Op B') G) :
    Prop :=
  t = p.map (lowMove k) ∨
    (∃ g q, x' = .wait g q ∧ t = p.map (lowMove k) ++ [.inl (.ask q)]) ∨
    ∃ g q n, x' = .wait g q ∧ p.map (lowMove k) = t ++ [.inl (.ans q (k q n))]

/-- What remains after a handler state: in sync, a call to forward, or an answer to return. -/
def Out : Reduction.State (ansH (F := E) (B' := B') k).toReduction →
    List (Move (Sig.mk E.Op B') G) → List (Move E G) → Pos (Sig.mk E.Op B') G → Prop
  | .idle, t, p, x' => C0 k t p x'
  | .wait _ _ _, t, p, x' => C0 k t p x'
  | .run q (.call _ _), t, p, x' =>
    (t = [] ∧ p = []) ∨ ∃ p', p = .inl (.ask q) :: p' ∧ C0 k t p' x'
  | .run q (.pure r), t, p, x' =>
    (t = [] ∧ p = []) ∨ ∃ t', t = .inl (.ans q r) :: t' ∧ C0 k t' p x'

/-- The matched states of the handler and positions of the strategy above. -/
inductive Inv : Reduction.State (ansH (F := E) (B' := B') k).toReduction →
    Pos (Sig.mk E.Op B') G → Prop
  | idle : Inv .idle .idle
  | run (g : G.Op) : Inv .idle (.run g)
  | ask (g : G.Op) (q : E.Op) : Inv (.run q (ansH k q)) (.wait g q)
  | fwd (g : G.Op) (q : E.Op) : Inv (.wait q q fun n => .pure (k q n)) (.wait g q)
  | ret (g : G.Op) (q : E.Op) (n : E.Ar q) : Inv (.run q (.pure (k q n))) (.wait g q)

variable {k}

theorem C0.cons {t : List (Move (Sig.mk E.Op B') G)} {p : List (Move E G)}
    {x' : Pos (Sig.mk E.Op B') G} (h : C0 k t p x') (o : Move E G) :
    C0 k (lowMove k o :: t) (o :: p) x' := by
  rcases h with rfl | ⟨g, q, hx, rfl⟩ | ⟨g, q, n, hx, h⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨g, q, hx, rfl⟩)
  · exact .inr (.inr ⟨g, q, n, hx, by simp [h]⟩)

theorem not_silent {x y : Reduction.State (ansH (F := E) (B' := B') k).toReduction} :
    ¬ (ansH k).toReduction.toLTS.step x none y := by
  intro hs
  cases hs with
  | tau hs => exact hs

theorem path_nil_eq {x x' : Pos (Sig.mk E.Op B') G} (h : Path x [] x') : x' = x := by
  cases h; rfl

/-- **The shape of an interaction with the relabelling handler below.** -/
theorem zip_out {w : List (Move E (Sig.mk E.Op B'))} {t : List (Move (Sig.mk E.Op B') G)}
    {p : List (Move E G)} (h : Zip w t p) :
    ∀ {z z' : Reduction.State (ansH (F := E) (B' := B') k).toReduction}
      {x x' : Pos (Sig.mk E.Op B') G},
      Inv k z x → (ansH k).toReduction.toLTS.Run z w z' → Path x t x' → Out k z t p x' := by
  induction h with
  | nil =>
    intro z z' x x' hi _ _
    cases hi with
    | idle => exact .inl rfl
    | run g => exact .inl rfl
    | ask g q => exact .inl ⟨rfl, rfl⟩
    | fwd g q => exact .inl rfl
    | ret g q n => exact .inl ⟨rfl, rfl⟩
  | left a _ ih =>
    intro z z' x x' hi hr hp
    obtain _ | ⟨hs, hr⟩ | ⟨hs, hr⟩ := hr
    · exact (not_silent hs).elim
    cases hi with
    | idle => cases hs
    | run g => cases hs
    | ask g q =>
      cases hs with
      | call hc =>
        cases hc
        exact .inr ⟨_, rfl, ih (.fwd g q) hr hp⟩
    | fwd g q =>
      cases hs with
      | resume _ _ _ n =>
        rcases ih (.ret g q n) hr hp with ⟨rfl, rfl⟩ | ⟨t', rfl, h⟩
        · exact .inr (.inr ⟨g, q, n, path_nil_eq hp, rfl⟩)
        · exact C0.cons h (.inl (.ans q n))
    | ret g q n =>
      cases hs with
      | call hc => cases hc
  | right c _ ih =>
    intro z z' x x' hi hr hp
    obtain _ | ⟨hs, hp⟩ := hp
    cases hi with
    | idle =>
      cases hs with
      | ask g => exact C0.cons (ih (.run g) hr hp) (.inr (.ask g))
    | run g =>
      cases hs with
      | ret g r => exact C0.cons (ih .idle hr hp) (.inr (.ans g r))
    | ask g q => cases hs
    | fwd g q => cases hs
    | ret g q n => cases hs
  | sync b _ ih =>
    intro z z' x x' hi hr hp
    obtain _ | ⟨hl, hr⟩ | ⟨hl, hr⟩ := hr
    · exact (not_silent hl).elim
    obtain _ | ⟨hs, hp⟩ := hp
    cases hi with
    | idle => cases hs
    | run g =>
      cases hl with
      | ask q =>
        cases hs with
        | call g q =>
          rcases ih (Inv.ask (k := k) g q) hr hp with ⟨rfl, rfl⟩ | ⟨p', rfl, h⟩
          · exact .inr (.inl ⟨g, q, path_nil_eq hp, rfl⟩)
          · exact C0.cons h (.inl (.ask q))
    | ask g q =>
      cases hl with
      | ret hd => cases hd
    | fwd g q => cases hl
    | ret g q n =>
      cases hl with
      | ret hd =>
        cases hd
        cases hs with
        | reply g q r => exact .inr ⟨_, rfl, ih (.run g) hr hp⟩

/-- The interaction from idle. -/
theorem zip_c0 {w : List (Move E (Sig.mk E.Op B'))} {t : List (Move (Sig.mk E.Op B') G)}
    {p : List (Move E G)} (h : Zip w t p) (hw : w ∈ Strategy.ofHandler (ansH k))
    {x' : Pos (Sig.mk E.Op B') G} (ht : Path .idle t x') : C0 k t p x' := by
  obtain ⟨z', hz⟩ := Strategy.mem_ofHandler.1 hw
  exact zip_out h .idle hz ht

theorem C0.length_le {t : List (Move (Sig.mk E.Op B') G)} {p : List (Move E G)}
    {x' : Pos (Sig.mk E.Op B') G} (h : C0 k t p x') :
    t.length ≤ p.length + 1 ∧ p.length ≤ t.length + 1 := by
  rcases h with rfl | ⟨-, -, -, rfl⟩ | ⟨g, q, n, -, hh⟩
  · simp
  · simp only [List.length_append, List.length_map, List.length_singleton]
    omega
  · have := congrArg List.length hh
    simp at this
    omega

/-- The lower trace of an interaction is at most its visible and upper traces. -/
theorem zip_length_left {α β γ : Type u} {s : List (α ⊕ β)} {t : List (β ⊕ γ)}
    {p : List (α ⊕ γ)} (h : Zip s t p) : s.length ≤ p.length + t.length := by
  induction h with
  | nil => simp
  | left a _ ih => simp; omega
  | right c _ ih => simp; omega
  | sync b _ ih => simp; omega

/-! ## The doubled play -/

variable (k) in
/-- The handler's moves for a visible play: each call is accepted and forwarded, each answer
received and returned relabelled. -/
def dblL : List (Move E G) → List (Move E (Sig.mk E.Op B'))
  | [] => []
  | .inr _ :: p => dblL p
  | .inl (.ask q) :: p => .inr (.ask q) :: .inl (.ask q) :: dblL p
  | .inl (.ans q n) :: p => .inl (.ans q n) :: .inr (.ans q (k q n)) :: dblL p

theorem zip_dblL (p : List (Move E G)) : Zip (dblL k p) (p.map (lowMove k)) p := by
  induction p with
  | nil => exact .nil
  | cons o p ih =>
    rcases o with (q | ⟨q, n⟩) | c
    · exact .sync _ (.left _ ih)
    · exact .left _ (.sync _ ih)
    · exact .right c ih

theorem dblL_append (p p' : List (Move E G)) : dblL k (p ++ p') = dblL k p ++ dblL k p' := by
  induction p with
  | nil => rfl
  | cons o p ih => rcases o with (q | ⟨q, n⟩) | c <;> simp [dblL, ih]

theorem dblL_prefix {p p' : List (Move E G)} (h : p <+: p') : dblL k p <+: dblL k p' := by
  obtain ⟨u, rfl⟩ := h
  rw [dblL_append]
  exact List.prefix_append _ _

variable (k) in
/-- The synchronised matches: no round in progress at the handler. -/
inductive Sync : Pos E G → Reduction.State (ansH (F := E) (B' := B') k).toReduction → Prop
  | idle : Sync .idle .idle
  | run (g : G.Op) : Sync (.run g) .idle
  | wait (g : G.Op) (q : E.Op) : Sync (.wait g q) (.wait q q fun n => .pure (k q n))

theorem run_dblL {x x' : Pos E G} {p : List (Move E G)} (h : Path x p x') :
    ∀ {z : Reduction.State (ansH (F := E) (B' := B') k).toReduction}, Sync k x z →
      ∃ z', (ansH k).toReduction.toLTS.Run z (dblL k p) z' := by
  induction h with
  | nil x => exact fun {z} _ => ⟨z, LTS.Run.nil (L := (ansH k).toReduction.toLTS) z⟩
  | cons hs _ ih =>
    intro z hz
    cases hs with
    | ask g =>
      cases hz
      exact ih (.run g)
    | call g q =>
      cases hz
      obtain ⟨z', hz'⟩ := ih (.wait g q)
      exact ⟨z', .vis (Reduction.Step.ask (R := (ansH k).toReduction) q) <|
        .vis (Reduction.Step.call (R := (ansH k).toReduction) (k := fun n => .pure (k q n)) rfl)
          hz'⟩
    | reply g q n =>
      cases hz
      obtain ⟨z', hz'⟩ := ih (.run g)
      exact ⟨z', .vis (Reduction.Step.resume (R := (ansH k).toReduction) q q _ n) <|
        .vis (Reduction.Step.ret (R := (ansH k).toReduction) (r := k q n) rfl) hz'⟩
    | ret g r =>
      cases hz
      exact ih .idle

theorem mem_dblL {p : List (Move E G)} (h : Legal p) :
    dblL k p ∈ Strategy.ofHandler (ansH k) := by
  obtain ⟨x', hx⟩ := h
  obtain ⟨z', hz⟩ := run_dblL hx .idle
  exact Strategy.mem_ofHandler.2 ⟨z', hz⟩

end Silmaril.Proofs.Games.AnsPull
