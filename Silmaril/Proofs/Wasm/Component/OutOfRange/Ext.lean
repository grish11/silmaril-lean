module

public import Silmaril.Proofs.Wasm.Component.OutOfRange.Trap
public import Silmaril.Wasm.Component.DWiringChatter2.Thms

/-!
# No chatter between a trap-silent handler and a trap-propagating node

In `ExtChatter e I L p` the environment `D` answers the node's calls forever
without a visible move (`w`). When `D = ofHandler h`, each such exchange is a
question answered at once, hence by a `pure` program of `h`
(`ofHandler_ask_ans`); for a trap-silent `h` that answer is `none`. Among four
exchanged events there is a question, its answer and one more event; the node
then moves below after a trap answer, which trap propagation forbids
(`not_extChatter_ofHandler`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.OutOfRange

open Silmaril.Games Silmaril.Wasm.Component

variable {X : Sig.{0}} {h : Handler X sigU} {N : DStrategy sigU sigU}

theorem exchange_false (hh : TrapSilent h) (hN : TrapPropagating N)
    {s₀ : List (Move X sigU)} {t₀ : List (Move sigU sigU)} {w₁ : List (Ev sigU)}
    {q q' : Nat × Payload} {r : Option Payload} {x : Ev sigU}
    (hD : s₀ ++ (w₁ ++ [Ev.ask q, Ev.ans q' r] : List (Ev sigU)).map .inr ∈
      Strategy.ofHandler h)
    (hL : t₀ ++ (w₁ ++ [.ask q, .ans q' r, x]).map .inl ∈ N.toStrategy) : False := by
  obtain ⟨-, hq⟩ := ofHandler_ask_ans (s := s₀ ++ w₁.map .inr) (by simpa using hD)
  obtain rfl := hh _ _ hq
  obtain ⟨g, hg⟩ := hN (t₀ ++ (w₁ ++ [Ev.ask q] : List (Ev sigU)).map .inl) q' (.inl x)
    (by simpa using hL)
  cases hg

/-- **A trap-silent handler and a trap-propagating node do not chatter.** -/
theorem not_extChatter_ofHandler (hh : TrapSilent h) (hN : TrapPropagating N) {e : Nat}
    {I : Set (List (Move X sigU))} (hI : I ∈ (DStrategy.ofHandler h).inf)
    {L : Set (List (Move sigU sigU))} (hL : L ∈ N.inf) {p : List (Move X sigU)} :
    ¬ ExtChatter e I L p := by
  rintro ⟨s₀, c₀, -, -, -, -, hw⟩
  obtain ⟨w, hk, hwI, hwL⟩ := hw 4
  generalize (Split.halves false (c₀.map (splitRoute e))).2 = t₀ at hwL
  have hD : ∀ u, u <+: s₀ ++ w.map .inr → u ∈ Strategy.ofHandler h := fun u hu =>
    (DStrategy.ofHandler h).toStrategy.of_prefix ((DStrategy.ofHandler h).inf_sub hI hwI) hu
  have hNp : ∀ u, u <+: t₀ ++ w.map .inl → u ∈ N.toStrategy := fun u hu =>
    N.toStrategy.of_prefix (N.inf_sub hL hwL) hu
  match w, hk, hD, hNp with
  | e₀ :: e₁ :: e₂ :: e₃ :: rest, _, hD, hNp =>
    cases e₀ with
    | ask q =>
      cases e₁ with
      | ask q' =>
        exact not_legal_upper_ask_ask (s := s₀) (q := q) (q' := q')
          ((Strategy.ofHandler h).legal (hD _ ⟨(e₂ :: e₃ :: rest).map .inr, by simp⟩))
      | ans q' r =>
        exact exchange_false hh hN (s₀ := s₀) (t₀ := t₀) (q := q) (q' := q') (r := r)
          (w₁ := []) (x := e₂)
          (hD _ ⟨(e₂ :: e₃ :: rest).map .inr, by simp⟩)
          (hNp _ ⟨(e₃ :: rest).map .inl, by simp⟩)
    | ans q₀ r₀ =>
      cases e₁ with
      | ans q' r' =>
        exact not_legal_upper_ans_ans (s := s₀) (r := r₀) (r' := r')
          ((Strategy.ofHandler h).legal (hD _ ⟨(e₂ :: e₃ :: rest).map .inr, by simp⟩))
      | ask q =>
        cases e₂ with
        | ask q' =>
          exact not_legal_upper_ask_ask (s := s₀ ++ [.inr (.ans q₀ r₀)]) (q := q) (q' := q')
            ((Strategy.ofHandler h).legal (hD _ ⟨(e₃ :: rest).map .inr, by simp⟩))
        | ans q' r =>
          exact exchange_false hh hN (s₀ := s₀) (t₀ := t₀) (q := q) (q' := q') (r := r)
            (w₁ := [.ans q₀ r₀]) (x := e₃)
            (hD _ ⟨(e₃ :: rest).map .inr, by simp⟩)
            (hNp _ ⟨rest.map .inl, by simp⟩)

end Silmaril.Proofs.Wasm.Component.OutOfRange
