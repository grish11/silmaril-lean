module

public import Silmaril.Games.Div.Defs
public import Silmaril.Games.Handler.Defs

/-!
# Relabelling the answers of a strategy

For a signature `F` and answer types `B' : F.Op → Type`, the signature `⟨F.Op, B'⟩` has the
operations of `F` with new answers. A family of maps `k q : F.Ar q → B' q` relabels moves
(`ansMove k`: an upper answer `n` to `q` becomes `k q n`; everything else is unchanged) and
divergence-observing strategies:

* `DStrategy.mapAns k σ : DStrategy E ⟨F.Op, B'⟩`: the plays, divergences and infinite plays of
  `σ`, relabelled. Only answers change, so Opponent moves (questions above, answers below) have
  preimages and receptiveness transfers. `k` need not be injective.
* `ansH k : Handler F ⟨F.Op, B'⟩`: the one-call handler forwarding each question `q` and
  returning `k q n` on the answer `n` (`Handler.ofHom ⟨id, k⟩`).

`Silmaril.Games.AnsMap.Thms` shows that composing with `ansH k` above is relabelling:
`σ.comp (DStrategy.ofHandler (ansH k)) = σ.mapAns k`. Answer translations between interfaces
with the same questions (a session interface `sig1 A B` and the Wasm interface `sigU`, whose
answers are `Option`s; the pairing of two sessions and the paired session) are of this form.
-/

@[expose] public section

namespace Silmaril.Games

universe u

variable {E F : Sig.{u}} {B' : F.Op → Type u}

/-- Relabel the answer of an upper move along `k`; other moves are unchanged. -/
def ansMove (k : (q : F.Op) → F.Ar q → B' q) : Move E F → Move E ⟨F.Op, B'⟩
  | .inl e => .inl e
  | .inr (.ask q) => .inr (.ask q)
  | .inr (.ans q n) => .inr (.ans q (k q n))

/-- The same position, at the relabelled interface. -/
def posAns : Pos E F → Pos E ⟨F.Op, B'⟩
  | .idle => .idle
  | .run q => .run q
  | .wait q m => .wait q m

/-- Relabelling answers preserves steps. -/
theorem step_ans (k : (q : F.Op) → F.Ar q → B' q) {x y : Pos E F} {o : Move E F}
    (h : Step x o y) : Step (posAns x) (ansMove k o) (posAns (B' := B') y) := by
  cases h <;> constructor

/-- Relabelling answers preserves paths. -/
theorem path_ans (k : (q : F.Op) → F.Ar q → B' q) {x y : Pos E F} {p : List (Move E F)}
    (h : Path x p y) : Path (posAns x) (p.map (ansMove k)) (posAns (B' := B') y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (step_ans k h) ih

/-- **The answer-relabelling handler**: forward the question `q`, return `k q n`. -/
def ansH (k : (q : F.Op) → F.Ar q → B' q) : Handler F ⟨F.Op, B'⟩ :=
  fun q => .call q fun n => .pure (k q n)

/-- The image of an infinite trace along a move map is an infinite trace. -/
theorem isInfPlay_image_ansMove (k : (q : F.Op) → F.Ar q → B' q)
    {I : Set (List (Move E F))} (hI : IsInfPlay I) :
    IsInfPlay (List.map (ansMove k) '' I) where
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
  unbounded n := by
    obtain ⟨s, hs, hn⟩ := hI.unbounded n
    exact ⟨_, ⟨s, hs, rfl⟩, by simpa using hn⟩

/-- **Relabel the answers of a strategy** along `k`: plays, divergences and infinite plays are
the images under `ansMove k`. -/
def DStrategy.mapAns (k : (q : F.Op) → F.Ar q → B' q) (σ : DStrategy E F) :
    DStrategy E ⟨F.Op, B'⟩ where
  toStrategy :=
    { plays := {p | ∃ q ∈ σ.toStrategy.plays, q.map (ansMove k) = p}
      nil_mem := ⟨[], σ.toStrategy.nil_mem, rfl⟩
      legal := by
        rintro _ ⟨q, hq, rfl⟩
        obtain ⟨y, hy⟩ := σ.toStrategy.legal hq
        exact ⟨_, path_ans k hy⟩
      of_prefix := by
        rintro s _ ⟨q, hq, rfl⟩ hs
        refine ⟨q.take s.length, σ.toStrategy.of_prefix hq (List.take_prefix _ _), ?_⟩
        rw [List.map_take]
        exact (List.prefix_iff_eq_take.1 hs).symm
      receptive := by
        rintro _ x y o ⟨q, hq, rfl⟩ hx hs ho
        obtain ⟨x₀, hx₀⟩ := σ.toStrategy.legal hq
        have hxx : posAns x₀ = x := Path.det (path_ans k hx₀) hx
        cases hs with
        | ask a =>
          cases x₀ <;> simp [posAns] at hxx
          exact ⟨_, σ.toStrategy.receptive hq hx₀ (Step.ask (E := E) (F := F) a) trivial,
            by simp [ansMove]⟩
        | reply a m n =>
          cases x₀ <;> simp [posAns] at hxx
          obtain ⟨rfl, rfl⟩ := hxx
          exact ⟨_, σ.toStrategy.receptive hq hx₀ (Step.reply (E := E) (F := F) _ _ n) trivial,
            by simp [ansMove]⟩
        | call => simp [Move.IsO] at ho
        | ret => simp [Move.IsO] at ho }
  div := {p | ∃ q ∈ σ.div, q.map (ansMove k) = p}
  inf := {K | ∃ J ∈ σ.inf, K = List.map (ansMove k) '' J}
  div_mem := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, σ.div_mem hq, rfl⟩
  div_run := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨a, ha⟩ := σ.div_run hq
    exact ⟨a, path_ans k ha⟩
  inf_isInf := by
    rintro _ ⟨J, hJ, rfl⟩
    exact isInfPlay_image_ansMove k (σ.inf_isInf hJ)
  inf_sub := by
    rintro _ ⟨J, hJ, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨q, σ.inf_sub hJ hq, rfl⟩

end Silmaril.Games
