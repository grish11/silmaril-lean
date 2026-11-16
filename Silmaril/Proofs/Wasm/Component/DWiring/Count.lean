module

public import Silmaril.Wasm.Component.DWiring.Defs
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.DivLTS.Thms

/-!
# One-call handlers make at most one move below per move above

* `nL`, `nR`: the numbers of left and right events of a trace; `Zip` relates
  them (`zip_counts`).
* `count_ofHandler`: a play `t` of a one-call handler has
  `nL t ≤ nR t + 1`. The invariant `Inv` tracks the state of the handler's
  transition system.
* `unbounded_p`: in an infinite interaction of any `δ` with a one-call handler
  on top, the visible part grows without bound; hence no hidden chatter.
* `unbounded_t`: in an infinite interaction of a one-call handler with any `σ`
  on top, `σ` moves forever.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiring

open Silmaril.Games Silmaril.Wasm.Component

universe u v w

/-! ## Counting events -/

/-- The number of left events. -/
def nL {α : Type u} {β : Type v} (s : List (α ⊕ β)) : ℕ := (s.filterMap Sum.getLeft?).length

/-- The number of right events. -/
def nR {α : Type u} {β : Type v} (s : List (α ⊕ β)) : ℕ :=
  (s.filterMap Sum.getRight?).length

section
variable {α : Type u} {β : Type v}

@[simp] theorem nL_nil : nL ([] : List (α ⊕ β)) = 0 := rfl
@[simp] theorem nR_nil : nR ([] : List (α ⊕ β)) = 0 := rfl
@[simp] theorem nL_inl (a : α) (s : List (α ⊕ β)) : nL (.inl a :: s) = nL s + 1 := rfl
@[simp] theorem nL_inr (b : β) (s : List (α ⊕ β)) : nL (.inr b :: s) = nL s := rfl
@[simp] theorem nR_inl (a : α) (s : List (α ⊕ β)) : nR (.inl a :: s) = nR s := rfl
@[simp] theorem nR_inr (b : β) (s : List (α ⊕ β)) : nR (.inr b :: s) = nR s + 1 := rfl

theorem length_eq (s : List (α ⊕ β)) : s.length = nL s + nR s := by
  induction s with
  | nil => rfl
  | cons x s ih => cases x <;> simp [ih] <;> omega

theorem nL_mono {s s' : List (α ⊕ β)} (h : s <+: s') : nL s ≤ nL s' := by
  obtain ⟨w, rfl⟩ := h
  simp only [nL, List.filterMap_append, List.length_append]
  omega

theorem nR_mono {s s' : List (α ⊕ β)} (h : s <+: s') : nR s ≤ nR s' := by
  obtain ⟨w, rfl⟩ := h
  simp only [nR, List.filterMap_append, List.length_append]
  omega
end

/-- How an interaction distributes events. -/
theorem zip_counts {α : Type u} {β : Type v} {γ : Type w} {s : List (α ⊕ β)}
    {t : List (β ⊕ γ)} {p : List (α ⊕ γ)} (h : Zip s t p) :
    nL s = nL p ∧ nR t = nR p ∧ nR s = nL t := by
  induction h with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | left a _ ih => simp [ih.1, ih.2.1, ih.2.2]
  | right c _ ih => simp [ih.1, ih.2.1, ih.2.2]
  | sync b _ ih => simp [ih.1, ih.2.1, ih.2.2]

/-! ## Plays of one-call handlers -/

variable {E F : Sig.{u}}

/-- A program making at most one call. -/
def OneProg {A : Type u} (c : Prog E A) : Prop :=
  (∃ r, c = .pure r) ∨ ∃ m k, c = .call m k ∧ ∀ n, ∃ r, k n = .pure r

/-- The counting invariant of a one-call handler. -/
def Inv (h : Handler E F) : h.toReduction.State → ℕ → ℕ → Prop
  | .idle, a, b => a ≤ b
  | .run _ c, a, b => (a + 1 ≤ b ∧ OneProg c) ∨ (a ≤ b + 1 ∧ ∃ r, c = .pure r)
  | .wait _ _ k, a, b => a ≤ b ∧ ∀ n, ∃ r, k n = .pure r

theorem inv_le {h : Handler E F} {x : h.toReduction.State} {a b : ℕ} (hx : Inv h x a b) :
    a ≤ b + 1 := by
  cases x with
  | idle => exact Nat.le_succ_of_le hx
  | run q c => rcases hx with ⟨hx, -⟩ | ⟨hx, -⟩ <;> omega
  | wait q m k => exact Nat.le_succ_of_le hx.1

theorem inv_step {h : Handler E F} (hh : OneCall h) {x y : h.toReduction.State}
    {o : Option (Move E F)} (hs : h.toReduction.toLTS.step x o y) {a b : ℕ} (hx : Inv h x a b) :
    Inv h y (a + nL o.toList) (b + nR o.toList) := by
  cases hs with
  | ask q =>
    simp only [Option.toList_some, nL_inr, nL_nil, nR_inr, nR_nil, Inv]
    exact .inl ⟨by simp only [Inv] at hx; omega, hh q⟩
  | tau hc => exact hc.elim
  | call hc =>
    simp only [Option.toList_some, nL_inl, nL_nil, nR_inl, nR_nil, Inv]
    change _ = Prog.call _ _ at hc
    subst hc
    rcases hx with ⟨hab, ⟨r, hr⟩ | ⟨m', k', hc, hk⟩⟩ | ⟨-, r, hr⟩
    · cases hr
    · cases hc
      exact ⟨by omega, hk⟩
    · cases hr
  | resume q m k n =>
    simp only [Option.toList_some, nL_inl, nL_nil, nR_inl, nR_nil, Inv]
    exact .inr ⟨by simp only [Inv] at hx; omega, hx.2 n⟩
  | ret hc =>
    simp only [Option.toList_some, nL_inr, nL_nil, nR_inr, nR_nil, Inv]
    rcases hx with ⟨hab, -⟩ | ⟨hab, -⟩ <;> omega

theorem inv_run {h : Handler E F} (hh : OneCall h) : ∀ {x y : h.toReduction.State}
    {s : List (Move E F)}, h.toReduction.toLTS.Run x s y →
    ∀ {a b : ℕ}, Inv h x a b → Inv h y (a + nL s) (b + nR s)
  | _, _, _, .nil _, _, _, hx => by simpa using hx
  | _, _, _, .tau hs hr, _, _, hx => by simpa using inv_run hh hr (by simpa using inv_step hh hs hx)
  | _, _, _, .vis (o := o) (s := s) hs hr, _, _, hx => by
    have := inv_run hh hr (inv_step hh hs hx)
    cases o <;> simp only [Option.toList_some, nL_inl, nL_inr, nR_inl, nR_inr, nL_nil,
      nR_nil] at this ⊢ <;> (convert this using 1; omega)

/-- **A one-call handler makes at most one move below per move above.** -/
theorem count_ofHandler {h : Handler E F} (hh : OneCall h) {t : List (Move E F)}
    (ht : t ∈ Strategy.ofHandler h) : nL t ≤ nR t + 1 := by
  obtain ⟨y, hr⟩ := Strategy.mem_ofHandler.1 ht
  have := inv_le (inv_run hh hr (a := 0) (b := 0) (show 0 ≤ 0 from le_rfl))
  simpa using this

/-! ## No chatter -/

/-- In an infinite interaction with a one-call handler on top, the visible part
grows without bound. -/
theorem unbounded_p {X : Sig.{u}} {h : Handler E F} (hh : OneCall h) {δ : DStrategy X E}
    (i : DStrategy.InfInteraction δ (DStrategy.ofHandler h)) : i.p.Unbounded := by
  intro k
  by_contra hk
  push Not at hk
  obtain ⟨n, hn⟩ := i.unbounded (4 * k + 3)
  have hz := zip_counts (i.zip n)
  have hc := count_ofHandler hh (i.mem_t n)
  have hp := length_eq (i.p n)
  have hs := length_eq (i.s n)
  have ht := length_eq (i.t n)
  have := hk n
  omega

/-- In an infinite interaction of a one-call handler with `σ` on top, `σ`
moves forever. -/
theorem unbounded_t {G : Sig.{u}} {h : Handler E F} (hh : OneCall h) {σ : DStrategy F G}
    (i : DStrategy.InfInteraction (DStrategy.ofHandler h) σ) (hp : i.p.Unbounded) :
    i.t.Unbounded := by
  intro k
  by_contra hk
  push Not at hk
  obtain ⟨n, hn⟩ := hp (2 * k + 2)
  have hz := zip_counts (i.zip n)
  have hc := count_ofHandler hh (i.mem_s n)
  have hp := length_eq (i.p n)
  have hs := length_eq (i.s n)
  have ht := length_eq (i.t n)
  have := hk n
  omega

end Silmaril.Proofs.Wasm.Component.DWiring
