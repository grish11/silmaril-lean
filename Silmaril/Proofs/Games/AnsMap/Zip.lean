module

public import Silmaril.Games.AnsMap.Defs
public import Silmaril.Games.Handler.Thms
public import Silmaril.Games.LTS.Thms

/-!
# Relabelling answers: interactions with the relabelling handler (proofs)

An interaction `Zip s w p` of a play `s` over `E ↠ F` with a play `w` of `ansH k` shows the
relabelled play `s.map (ansMove k)`, up to the round in progress at the handler: it may have
accepted a question `q` not yet forwarded (`p` has one more move, the question), or received an
answer not yet returned (`p` has one move less). In both cases `s` ends idle (`zip_out`, with
the shape of the remaining moves for each handler state in `Out`). Conversely the doubling
`dblW s` of `s` is a play of the handler (`run_dblW`) interacting with `s` to show its
relabelling (`zip_dblW`).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.AnsMap

open Silmaril.Games

universe u

variable {E F : Sig.{u}} {B' : F.Op → Type u} (k : (q : F.Op) → F.Ar q → B' q)

/-- The visible play is the relabelled play, or adds a question the handler has not forwarded, or
lacks an answer the handler has not returned. -/
def C0 (s : List (Move E F)) (p : List (Move E (Sig.mk F.Op B'))) (x' : Pos E F) : Prop :=
  p = s.map (ansMove k) ∨ (x' = .idle ∧ ((∃ q, p = s.map (ansMove k) ++ [.inr (.ask q)]) ∨
    ∃ o, s.map (ansMove k) = p ++ [o]))

/-- What remains after a handler state: in sync, a forwarded question pending, or an answer to
return. -/
def Out : Reduction.State (ansH (B' := B') k).toReduction → List (Move E F) →
    List (Move E (Sig.mk F.Op B')) →
    Pos E F → Prop
  | .idle, s, p, x' => C0 k s p x'
  | .wait _ _ _, s, p, x' => C0 k s p x'
  | .run q (.call _ _), s, p, x' =>
    (s = [] ∧ p = []) ∨ ∃ s', s = .inr (.ask q) :: s' ∧ C0 k s' p x'
  | .run q (.pure r), s, p, x' =>
    (s = [] ∧ p = []) ∨ ∃ p', p = .inr (.ans q r) :: p' ∧ C0 k s p' x'

/-- The matched positions of the strategy and states of the handler. -/
inductive Inv : Pos E F → Reduction.State (ansH (B' := B') k).toReduction → Prop
  | idle : Inv .idle .idle
  | ask (q : F.Op) : Inv .idle (.run q (ansH k q))
  | run (q : F.Op) : Inv (.run q) (.wait q q fun n => .pure (k q n))
  | wait (q : F.Op) (m : E.Op) : Inv (.wait q m) (.wait q q fun n => .pure (k q n))
  | ret (q : F.Op) (n : F.Ar q) : Inv .idle (.run q (.pure (k q n)))

variable {k}

theorem C0.cons {s : List (Move E F)} {p : List (Move E (Sig.mk F.Op B'))} {x' : Pos E F}
    (h : C0 k s p x')
    (o : Move E F) : C0 k (o :: s) (ansMove k o :: p) x' := by
  rcases h with rfl | ⟨hx, ⟨q, rfl⟩ | ⟨o', h⟩⟩
  · exact .inl rfl
  · exact .inr ⟨hx, .inl ⟨q, rfl⟩⟩
  · exact .inr ⟨hx, .inr ⟨o', by simp [h]⟩⟩

theorem not_silent {x y : Reduction.State (ansH (B' := B') k).toReduction} :
    ¬ (ansH k).toReduction.toLTS.step x none y := by
  intro hs
  cases hs with
  | tau hs => exact hs

theorem path_nil_idle {x' : Pos E F} (h : Path (.idle : Pos E F) [] x') : x' = .idle := by
  cases h; rfl

/-- **The shape of an interaction with the relabelling handler.** -/
theorem zip_out {s : List (Move E F)} {w : List (Move F (Sig.mk F.Op B'))}
    {p : List (Move E (Sig.mk F.Op B'))}
    (h : Zip s w p) : ∀ {x x' : Pos E F} {z z' : Reduction.State (ansH (B' := B') k).toReduction},
      Inv k x z → Path x s x' → (ansH k).toReduction.toLTS.Run z w z' → Out k z s p x' := by
  induction h with
  | nil =>
    intro x x' z z' hi _ _
    cases hi with
    | idle => exact .inl rfl
    | ask q => exact .inl ⟨rfl, rfl⟩
    | run q => exact .inl rfl
    | wait q m => exact .inl rfl
    | ret q n => exact .inl ⟨rfl, rfl⟩
  | left a _ ih =>
    intro x x' z z' hi hp hr
    obtain _ | ⟨hs, hp⟩ := hp
    cases hi with
    | idle => cases hs
    | ask q => cases hs
    | ret q n => cases hs
    | run q =>
      cases hs with
      | call q m => exact C0.cons (ih (.wait q m) hp hr) (.inl (.ask m))
    | wait q m =>
      cases hs with
      | reply q m n => exact C0.cons (ih (.run q) hp hr) (.inl (.ans m n))
  | right c _ ih =>
    intro x x' z z' hi hp hr
    obtain _ | ⟨hs, hr⟩ | ⟨hs, hr⟩ := hr
    · exact (not_silent hs).elim
    cases hi with
    | idle =>
      cases hs with
      | ask q =>
        rcases ih (Inv.ask (k := k) q) hp hr with ⟨rfl, rfl⟩ | ⟨s', rfl, h⟩
        · exact .inr ⟨path_nil_idle hp, .inl ⟨q, rfl⟩⟩
        · exact C0.cons h (.inr (.ask q))
    | ask q =>
      cases hs with
      | ret hd => cases hd
    | run q => cases hs
    | wait q m => cases hs
    | ret q n =>
      cases hs with
      | ret hd =>
        cases hd
        exact .inr ⟨_, rfl, ih .idle hp hr⟩
  | sync b _ ih =>
    intro x x' z z' hi hp hr
    obtain _ | ⟨hs, hp⟩ := hp
    obtain _ | ⟨hl, hr⟩ | ⟨hl, hr⟩ := hr
    · exact (not_silent hl).elim
    cases hi with
    | idle => cases hl
    | ask q =>
      cases hl with
      | call hc =>
        cases hc
        cases hs with
        | ask q => exact .inr ⟨_, rfl, ih (.run q) hp hr⟩
    | run q =>
      cases hl with
      | resume _ _ _ n =>
        cases hs with
        | ret q r =>
          rcases ih (.ret q n) hp hr with ⟨rfl, rfl⟩ | ⟨p', rfl, h⟩
          · exact .inr ⟨path_nil_idle hp, .inr ⟨_, rfl⟩⟩
          · exact C0.cons h (.inr (.ans q n))
    | wait q m =>
      cases hl with
      | resume _ _ _ n => cases hs
    | ret q n =>
      cases hl with
      | call hc => cases hc

/-- The interaction from idle. -/
theorem zip_c0 {s : List (Move E F)} {w : List (Move F (Sig.mk F.Op B'))}
    {p : List (Move E (Sig.mk F.Op B'))}
    (h : Zip s w p) {x' : Pos E F} (hs : Path .idle s x') (hw : w ∈ Strategy.ofHandler (ansH k)) :
    C0 k s p x' := by
  obtain ⟨z', hz⟩ := Strategy.mem_ofHandler.1 hw
  exact zip_out h .idle hs hz

theorem C0.length_le {s : List (Move E F)} {p : List (Move E (Sig.mk F.Op B'))} {x' : Pos E F}
    (h : C0 k s p x') : s.length ≤ p.length + 1 ∧ p.length ≤ s.length + 1 := by
  rcases h with rfl | ⟨-, ⟨q, rfl⟩ | ⟨o, h⟩⟩
  · simp
  · simp only [List.length_append, List.length_map, List.length_singleton]
    omega
  · have := congrArg List.length h
    simp at this
    omega

/-- Hidden moves are at most the moves of the lower play. -/
theorem zip_length {α β γ : Type u} {s : List (α ⊕ β)} {w : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s w p) : w.length ≤ p.length + s.length := by
  induction h with
  | nil => simp
  | left a _ ih => simp; omega
  | right c _ ih => simp; omega
  | sync b _ ih => simp; omega

/-! ## The doubled play -/

variable (k) in
/-- The handler's moves for a play: each question is accepted and forwarded, each answer received
and returned relabelled. -/
def dblW : List (Move E F) → List (Move F (Sig.mk F.Op B'))
  | [] => []
  | .inl _ :: s => dblW s
  | .inr (.ask q) :: s => .inr (.ask q) :: .inl (.ask q) :: dblW s
  | .inr (.ans q n) :: s => .inl (.ans q n) :: .inr (.ans q (k q n)) :: dblW s

theorem zip_dblW (s : List (Move E F)) : Zip s (dblW k s) (s.map (ansMove k)) := by
  induction s with
  | nil => exact .nil
  | cons o s ih =>
    rcases o with e | (q | ⟨q, n⟩)
    · exact .left e ih
    · exact .right _ (.sync _ ih)
    · exact .sync _ (.right _ ih)

theorem dblW_append (s t : List (Move E F)) : dblW k (s ++ t) = dblW k s ++ dblW k t := by
  induction s with
  | nil => rfl
  | cons o s ih => rcases o with e | (q | ⟨q, n⟩) <;> simp [dblW, ih]

theorem dblW_prefix {s t : List (Move E F)} (h : s <+: t) : dblW k s <+: dblW k t := by
  obtain ⟨u, rfl⟩ := h
  rw [dblW_append]
  exact List.prefix_append _ _

variable (k) in
/-- The synchronised matches: no round in progress at the handler. -/
inductive Sync : Pos E F → Reduction.State (ansH (B' := B') k).toReduction → Prop
  | idle : Sync .idle .idle
  | run (q : F.Op) : Sync (.run q) (.wait q q fun n => .pure (k q n))
  | wait (q : F.Op) (m : E.Op) : Sync (.wait q m) (.wait q q fun n => .pure (k q n))

theorem run_dblW {x x' : Pos E F} {s : List (Move E F)} (h : Path x s x') :
    ∀ {z : Reduction.State (ansH (B' := B') k).toReduction}, Sync k x z →
      ∃ z', (ansH k).toReduction.toLTS.Run z (dblW k s) z' := by
  induction h with
  | nil x => exact fun {z} _ => ⟨z, LTS.Run.nil (L := (ansH k).toReduction.toLTS) z⟩
  | cons hs _ ih =>
    intro z hz
    cases hs with
    | ask q =>
      cases hz
      obtain ⟨z', hz'⟩ := ih (.run q)
      exact ⟨z', .vis (Reduction.Step.ask (R := (ansH k).toReduction) q) <|
        .vis (Reduction.Step.call (R := (ansH k).toReduction) (k := fun n => .pure (k q n)) rfl)
          hz'⟩
    | call q m =>
      cases hz
      exact ih (.wait q m)
    | reply q m n =>
      cases hz
      exact ih (.run q)
    | ret q n =>
      cases hz
      obtain ⟨z', hz'⟩ := ih .idle
      exact ⟨z', .vis (Reduction.Step.resume (R := (ansH k).toReduction) q q _ n) <|
        .vis (Reduction.Step.ret (R := (ansH k).toReduction) (r := k q n) rfl) hz'⟩

theorem mem_dblW {s : List (Move E F)} (h : Legal s) : dblW k s ∈ Strategy.ofHandler (ansH k) := by
  obtain ⟨x', hx⟩ := h
  obtain ⟨z', hz⟩ := run_dblW hx .idle
  exact Strategy.mem_ofHandler.2 ⟨z', hz⟩

end Silmaril.Proofs.Games.AnsMap
