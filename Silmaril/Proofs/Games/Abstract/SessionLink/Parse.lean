module

public import Silmaril.Proofs.Games.Abstract.SessionLink.Run
public import Silmaril.Games.Zip.Defs
public import Mathlib.Data.Nat.Find
import Mathlib.Data.List.Basic

/-!
# Linking sessions: lists of moves (proofs)

* parsing session rounds: a prefix relation between completed rounds followed by partial rounds
  cancels the common rounds (`parse`), and call moves determine their calls
  (`callMoves_prefix_inv`, `prefix_callMoves`);
* projections of interactions: the hidden events of both sides agree (`upper_eq_lower`), and the
  visible upper events are the upper component's (`upper_vis`);
* a prefix of the upper side of an interaction is the upper side of a prefix (`zip_prefix_right`);
* streams: prepending a list, and flattening infinitely many lists.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.SessionLink

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
  Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession

universe u

variable {E F : Sig.{u}} {A B : Type u}

/-! ## Call moves -/

theorem call_eq_of_ans {x x' : Call E} (h : (Ev.ans x.1 x.2 : Ev E) = Ev.ans x'.1 x'.2) :
    x = x' := by
  obtain ⟨m, n⟩ := x
  obtain ⟨m', n'⟩ := x'
  simp only [Ev.ans.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases h
  rfl

/-- **Call moves determine their calls**, up to a following answer or a call. -/
theorem callMoves_prefix_inv {c c' : List (Call E)} {M Y : List (Move E F)}
    (hY : ∀ e Y', Y ≠ .inl e :: Y') (h : callMoves c ++ M <+: callMoves c' ++ Y) :
    c <+: c' ∧ ∀ m, M = [.inl (.ask m)] → CallPre c m c' := by
  induction c generalizing c' with
  | nil =>
    refine ⟨List.nil_prefix, fun m hM => ?_⟩
    subst hM
    rcases c' with _ | ⟨x, c'⟩
    · obtain ⟨r, hr⟩ := h
      exact absurd hr.symm (hY _ _)
    · obtain ⟨r, hr⟩ := h
      simp at hr
      obtain ⟨rfl, -⟩ := hr
      exact ⟨x.2, c', rfl⟩
  | cons x c ih =>
    rcases c' with _ | ⟨x', c'⟩
    · obtain ⟨r, hr⟩ := h
      exact absurd hr.symm (by simpa using hY _ _)
    · simp only [callMoves_cons, List.cons_append, List.cons_prefix_cons] at h
      obtain ⟨-, h₂, h⟩ := h
      have hx : x = x' := call_eq_of_ans (Sum.inl.inj h₂)
      subst hx
      obtain ⟨h₁, h₂⟩ := ih h
      exact ⟨List.cons_prefix_cons.2 ⟨rfl, h₁⟩, fun m hM => by
        obtain ⟨n, r, hr⟩ := h₂ m hM
        exact ⟨n, r, by simp [hr]⟩⟩

/-- Call moves followed by an answer of the upper side determine the calls and the answer. -/
theorem callMoves_inr {c c' : List (Call E)} {o o' : Ev F} {X Y : List (Move E F)}
    (h : callMoves c ++ .inr o :: X <+: callMoves c' ++ .inr o' :: Y) :
    c = c' ∧ o = o' ∧ X <+: Y := by
  induction c generalizing c' with
  | nil =>
    rcases c' with _ | ⟨x, c'⟩
    · simp only [callMoves_nil, List.nil_append, List.cons_prefix_cons, Sum.inr.injEq] at h
      exact ⟨rfl, h.1, h.2⟩
    · simp at h
  | cons x c ih =>
    rcases c' with _ | ⟨x', c'⟩
    · simp at h
    · simp only [callMoves_cons, List.cons_append, List.cons_prefix_cons] at h
      obtain ⟨-, h₂, h⟩ := h
      have hx : x = x' := call_eq_of_ans (Sum.inl.inj h₂)
      subst hx
      obtain ⟨rfl, h₁, h₂⟩ := ih h
      exact ⟨rfl, h₁, h₂⟩

/-- A prefix of call moves is call moves, possibly followed by the next call. -/
theorem prefix_callMoves {Q : List (Move E F)} {D : List (Call E)}
    (h : Q <+: callMoves D) :
    ∃ j, j ≤ D.length ∧ (Q = callMoves (D.take j) ∨
      ∃ hj : j < D.length, Q = callMoves (D.take j) ++ [.inl (.ask (D[j]'hj).1)]) := by
  induction D generalizing Q with
  | nil => exact ⟨0, le_rfl, .inl (by simpa using h)⟩
  | cons x D ih =>
    simp only [callMoves_cons] at h
    rcases List.prefix_cons_iff.1 h with rfl | ⟨Q₁, rfl, h₁⟩
    · exact ⟨0, by simp, .inl rfl⟩
    rcases List.prefix_cons_iff.1 h₁ with rfl | ⟨Q₂, rfl, h₂⟩
    · exact ⟨0, by simp, .inr ⟨by simp, by simp⟩⟩
    obtain ⟨j, hj, h⟩ := ih h₂
    refine ⟨j + 1, by simp; omega, ?_⟩
    rcases h with rfl | ⟨hj', rfl⟩
    · exact .inl (by simp)
    · exact .inr ⟨by simp; omega, by simp⟩

/-! ## Parsing session rounds -/

/-- A partial round: empty, or a question followed by lower moves. -/
def PTail (T : List (Move E (sig1 A B))) : Prop := ∀ o ∈ T.tail, o.isLeft

theorem sroundMoves_append (r : A × List (Call E) × (B ⊕ PUnit.{u + 1}))
    (X : List (Move E (sig1 A B))) :
    sroundMoves r ++ X = .inr (.ask r.1) :: (callMoves r.2.1 ++ .inr (.ans r.1 r.2.2) :: X) := by
  simp [sroundMoves]

/-- **Parsing**: completed rounds followed by a partial round, as a prefix of completed rounds
followed by a partial round, are an initial segment of the rounds. -/
theorem parse {R R' : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))}
    {T T' : List (Move E (sig1 A B))} (hT' : PTail T')
    (h : sroundsMoves R ++ T <+: sroundsMoves R' ++ T') :
    ∃ R'', R' = R ++ R'' ∧ T <+: sroundsMoves R'' ++ T' := by
  induction R generalizing R' with
  | nil => exact ⟨R', rfl, by simpa using h⟩
  | cons r R ih =>
    rcases R' with _ | ⟨r', R'⟩
    · exfalso
      obtain ⟨a, c, x⟩ := r
      simp only [sroundsMoves_cons, sroundsMoves_nil, List.nil_append, List.append_assoc] at h
      simp only [sroundMoves_append] at h
      obtain ⟨Z, hZ⟩ := h
      have hmem : (Sum.inr (Ev.ans a x) : Move E (sig1 A B)) ∈ T'.tail := by
        rw [← hZ]; simp
      simpa using hT' _ hmem
    · obtain ⟨a, c, x⟩ := r
      obtain ⟨a', c', x'⟩ := r'
      simp only [sroundsMoves_cons, List.append_assoc] at h
      simp only [sroundMoves_append, List.cons_prefix_cons, Sum.inr.injEq, Ev.ask.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, ho, hX⟩ := callMoves_inr h
      simp only [Ev.ans.injEq, heq_eq_eq, true_and] at ho
      subst ho
      obtain ⟨R'', rfl, hT⟩ := ih hX
      exact ⟨R'', rfl, hT⟩

/-! ## Projections -/

theorem upper_append {E F : Sig.{u}} (s t : List (Move E F)) :
    upper (s ++ t) = upper s ++ upper t := by
  simp [upper, List.filterMap_append]

theorem lower_append {E F : Sig.{u}} (s t : List (Move E F)) :
    lower (s ++ t) = lower s ++ lower t := by
  simp [lower, List.filterMap_append]

@[simp] theorem upper_cons_inl {E F : Sig.{u}} (e : Ev E) (s : List (Move E F)) :
    upper (.inl e :: s) = upper s := rfl

@[simp] theorem upper_cons_inr {E F : Sig.{u}} (e : Ev F) (s : List (Move E F)) :
    upper (.inr e :: s) = e :: upper s := rfl

@[simp] theorem lower_cons_inl {E F : Sig.{u}} (e : Ev E) (s : List (Move E F)) :
    lower (.inl e :: s) = e :: lower s := rfl

@[simp] theorem lower_cons_inr {E F : Sig.{u}} (e : Ev F) (s : List (Move E F)) :
    lower (.inr e :: s) = lower s := rfl

@[simp] theorem upper_nil {E F : Sig.{u}} : upper ([] : List (Move E F)) = [] := rfl

@[simp] theorem lower_nil {E F : Sig.{u}} : lower ([] : List (Move E F)) = [] := rfl

@[simp] theorem upper_callMoves (c : List (Call E)) : upper (callMoves c : List (Move E F)) = [] := by
  induction c with
  | nil => rfl
  | cons x c ih => exact ih

@[simp] theorem length_lower_callMoves (c : List (Call E)) :
    (lower (callMoves c : List (Move E F))).length = 2 * c.length := by
  induction c with
  | nil => rfl
  | cons x c ih => simp [ih]; omega

theorem length_upper_sroundsMoves (R : List (A × List (Call E) × (B ⊕ PUnit.{u + 1}))) :
    (upper (sroundsMoves R : List (Move E (sig1 A B)))).length = 2 * R.length := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    rw [sroundsMoves_cons, upper_append, List.length_append, ih]
    simp [sroundMoves, upper_append]; omega

theorem length_lower_sroundsMoves (R : List (A × List (Call F) × (B ⊕ PUnit.{u + 1}))) :
    (lower (sroundsMoves R : List (Move F (sig1 A B)))).length =
      2 * (R.flatMap fun r => r.2.1).length := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    rw [sroundsMoves_cons, lower_append, List.length_append, ih]
    simp [sroundMoves, lower_append]; omega

theorem length_upper_le {E F : Sig.{u}} {s t : List (Move E F)} (h : s <+: t) :
    (upper s).length ≤ (upper t).length :=
  (h.filterMap _).length_le

theorem length_lower_le {E F : Sig.{u}} {s t : List (Move E F)} (h : s <+: t) :
    (lower s).length ≤ (lower t).length :=
  (h.filterMap _).length_le

/-- **The hidden events of both sides of an interaction agree.** -/
theorem upper_eq_lower {G : Sig.{u}} {s : List (Move E F)} {t : List (Move F G)}
    {p : List (Move E G)} (h : Zip s t p) : upper s = lower t := by
  induction h with
  | nil => rfl
  | left a _ ih => exact ih
  | right c _ ih => exact ih
  | sync b _ ih => simp [ih]

/-- **The visible upper events are those of the upper side.** -/
theorem upper_vis {G : Sig.{u}} {s : List (Move E F)} {t : List (Move F G)}
    {p : List (Move E G)} (h : Zip s t p) : upper p = upper t := by
  induction h with
  | nil => rfl
  | left a _ ih => exact ih
  | right c _ ih => simp [ih]
  | sync b _ ih => exact ih

/-- **A prefix of the upper side of an interaction is the upper side of a prefix.** -/
theorem zip_prefix_right {G : Sig.{u}} {s : List (Move E F)} {t : List (Move F G)}
    {p : List (Move E G)} (h : Zip s t p) {t' : List (Move F G)} (ht : t' <+: t) :
    ∃ s' p', s' <+: s ∧ p' <+: p ∧ Zip s' t' p' := by
  induction h generalizing t' with
  | nil => exact ⟨[], [], List.nil_prefix, List.nil_prefix, by rw [List.prefix_nil.1 ht]; exact .nil⟩
  | left a _ ih =>
    obtain ⟨s', p', hs, hp, hz⟩ := ih ht
    exact ⟨_, _, List.cons_prefix_cons.2 ⟨rfl, hs⟩, List.cons_prefix_cons.2 ⟨rfl, hp⟩, .left a hz⟩
  | right c _ ih =>
    rcases List.prefix_cons_iff.1 ht with rfl | ⟨t₁, rfl, ht₁⟩
    · exact ⟨[], [], List.nil_prefix, List.nil_prefix, .nil⟩
    · obtain ⟨s', p', hs, hp, hz⟩ := ih ht₁
      exact ⟨_, _, hs, List.cons_prefix_cons.2 ⟨rfl, hp⟩, .right c hz⟩
  | sync b _ ih =>
    rcases List.prefix_cons_iff.1 ht with rfl | ⟨t₁, rfl, ht₁⟩
    · exact ⟨[], [], List.nil_prefix, List.nil_prefix, .nil⟩
    · obtain ⟨s', p', hs, hp, hz⟩ := ih ht₁
      exact ⟨_, _, List.cons_prefix_cons.2 ⟨rfl, hs⟩, hp, .sync b hz⟩

/-- Two prefixes of a play ending with an upper move, with as many upper moves before, are
equal. -/
theorem eq_of_upper {E F : Sig.{u}} {X Y Z : List (Move E F)} {g g' : Ev F}
    (hX : X ++ [.inr g] <+: Z) (hY : Y ++ [.inr g'] <+: Z)
    (h : (upper X).length = (upper Y).length) : X = Y ∧ g = g' := by
  have key : ∀ {X Y : List (Move E F)} {g g' : Ev F}, X ++ [.inr g] <+: Y ++ [.inr g'] →
      (upper X).length = (upper Y).length → X = Y ∧ g = g' := by
    intro X Y g g' hp hl
    rcases List.prefix_concat_iff.1 hp with h | h
    · obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
      exact ⟨h₁, by simpa using h₂⟩
    · have := length_upper_le h
      simp [upper_append] at this; omega
  rcases List.prefix_or_prefix_of_prefix hX hY with hp | hp
  · exact key hp h
  · obtain ⟨h₁, h₂⟩ := key hp h.symm
    exact ⟨h₁.symm, h₂.symm⟩

/-! ## Streams -/

theorem streamTake_add {α : Type u} (f : ℕ → α) (N j : ℕ) :
    streamTake f (N + j) = streamTake f N ++ streamTake (fun i => f (N + i)) j := by
  induction j with
  | zero => simp
  | succ j ih => rw [← Nat.add_assoc, streamTake_succ, ih, streamTake_succ, List.append_assoc]

/-- A list followed by a stream. -/
def prependStream {α : Type u} (L : List α) (ω : ℕ → α) : ℕ → α :=
  fun k => if h : k < L.length then L[k] else ω (k - L.length)

theorem streamTake_prependStream {α : Type u} (L : List α) (ω : ℕ → α) (k : ℕ) :
    streamTake (prependStream L ω) (L.length + k) = L ++ streamTake ω k := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [streamTake, List.getElem_ofFn, prependStream]
    rw [List.getElem_append]
    split_ifs with h
    · rfl
    · simp

/-- The flattening of infinitely many lists, infinitely many of them nonempty. -/
noncomputable def flatStream {α : Type u} (l : ℕ → List α) (hl : ∀ n, ∃ k, n < (streamTake l k).flatten.length) :
    ℕ → α :=
  fun j => ((streamTake l (Nat.find (hl j))).flatten)[j]'(Nat.find_spec (hl j))

theorem streamTake_flatStream {α : Type u} (l : ℕ → List α)
    (hl : ∀ n, ∃ k, n < (streamTake l k).flatten.length) (k : ℕ) :
    streamTake (flatStream l hl) (streamTake l k).flatten.length = (streamTake l k).flatten := by
  have hmono : ∀ {i j}, i ≤ j → (streamTake l i).flatten <+: (streamTake l j).flatten :=
    fun h => by
      obtain ⟨r, hr⟩ := streamTake_prefix l h
      exact ⟨r.flatten, by rw [← hr, List.flatten_append]⟩
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    have e : (streamTake (flatStream l hl) (streamTake l k).flatten.length)[j]'h₁ =
        flatStream l hl j := by simp [streamTake]
    rw [e]
    unfold flatStream
    rcases le_total (Nat.find (hl j)) k with h | h
    · exact (hmono h).getElem _
    · exact ((hmono h).getElem _).symm

end Silmaril.Proofs.Games.Abstract.SessionLink
