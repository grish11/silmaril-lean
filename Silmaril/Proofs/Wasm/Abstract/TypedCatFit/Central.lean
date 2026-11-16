module

public import Silmaril.Proofs.Wasm.Abstract.TypedCatFit.Tensor
public import Silmaril.Proofs.Wasm.Abstract.TypedCat.Interchange

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCatFit.Thms`: **pure morphisms below commute with typed
morphisms on top.** `TypedCat.interchange_of_pure` puts the pure morphism on top. Here it is
below (`rightR`), and the morphism `g₁` on top is arbitrary but falls through at a fixed height
`n'` from the state considered; then both orders are `g₁` on the top `n` values with the pure
image of the `m` values below appended (`whiskO`). A pure morphism keeps the store and frame and
always falls through, so `g₁` runs from the same state in both orders. Typed code under an oracle
whose fitting answers respect arities falls through at its target's height (`GoodO`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCatFit

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Proofs.Wasm.Abstract.TypedCat (isNormal_inv)
open Silmaril.Proofs.Wasm.Abstract.ExposePTyped (whiskO_abrupt)

variable {H : Type}

theorem whiskO_normal_inv {rest w : List Val} {o : POut}
    (h : POut.flow (.normal w) = whiskO rest o) : ∃ ws, o = .flow (.normal ws) ∧ w = ws ++ rest := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;> simp [whiskO] at h
  exact ⟨vs, rfl, h⟩

section Below

variable {m m' n n' : Nat} {ψ : List Val → List Val} {g₁ g₂ : ORel H} {s : Store H} {f : Frame}
  {stk : List Val}

theorem below_lhs_iff (hp : PureAt m m' ψ g₂) (hl : stk.length = n + m)
    (hh : ∀ s' f' vs, g₁ s f (stk.take n) s' f' (.flow (.normal vs)) → vs.length = n')
    {s' : Store H} {f' : Frame} {o : POut} :
    seqR (leftR n g₁) (rightR n' g₂) s f stk s' f' o ↔
      ∃ o₁, g₁ s f (stk.take n) s' f' o₁ ∧ o = whiskO (ψ (stk.drop n)) o₁ := by
  have hn : n ≤ stk.length := by omega
  have hD : (stk.drop n).length = m := by simp only [List.length_drop]; omega
  constructor
  · rintro (⟨s₁, f₁, vs, ⟨-, o₁, h₁, hv⟩, ⟨-, o₂, h₂, rfl⟩⟩ | ⟨⟨-, o₁, h₁, rfl⟩, hnn⟩)
    · obtain ⟨ws, rfl, rfl⟩ := whiskO_normal_inv hv
      have hw := hh _ _ _ h₁
      rw [List.drop_left' hw] at h₂
      obtain ⟨rfl, rfl, rfl⟩ := (hp.2 _ _ _ _ _ _ hD).1 h₂
      refine ⟨_, h₁, ?_⟩
      rw [List.take_left' hw]
      rfl
    · have hn₁ : ¬ o₁.IsNormal := fun hN => by
        obtain ⟨ws, rfl⟩ := isNormal_inv hN
        exact hnn trivial
      exact ⟨o₁, h₁, by rw [whiskO_abrupt hn₁, whiskO_abrupt hn₁]⟩
  · rintro ⟨o₁, h₁, rfl⟩
    by_cases hN : o₁.IsNormal
    · obtain ⟨ws, rfl⟩ := isNormal_inv hN
      have hw := hh _ _ _ h₁
      refine .inl ⟨s', f', ws ++ stk.drop n, ⟨hn, _, h₁, rfl⟩,
        ⟨by simp; omega, .flow (.normal (ψ (stk.drop n))), ?_, ?_⟩⟩
      · rw [List.drop_left' hw]
        exact (hp.2 _ _ _ _ _ _ hD).2 ⟨rfl, rfl, rfl⟩
      · rw [List.take_left' hw]
        rfl
    · refine .inr ⟨⟨hn, o₁, h₁, ?_⟩, ?_⟩
      · rw [whiskO_abrupt hN, whiskO_abrupt hN]
      · rw [whiskO_abrupt hN]; exact hN

theorem below_rhs_iff (hp : PureAt m m' ψ g₂) (hl : stk.length = n + m)
    {s' : Store H} {f' : Frame} {o : POut} :
    seqR (rightR n g₂) (leftR n g₁) s f stk s' f' o ↔
      ∃ o₁, g₁ s f (stk.take n) s' f' o₁ ∧ o = whiskO (ψ (stk.drop n)) o₁ := by
  have hn : n ≤ stk.length := by omega
  have hD : (stk.drop n).length = m := by simp only [List.length_drop]; omega
  have hT := Interp.take_length_of_le hn
  constructor
  · rintro (⟨s₁, f₁, vs, ⟨-, o₂, h₂, hv⟩, ⟨-, o₁, h₁, rfl⟩⟩ | ⟨⟨-, o₂, h₂, rfl⟩, hnn⟩)
    · obtain ⟨rfl, rfl, rfl⟩ := (hp.2 _ _ _ _ _ _ hD).1 h₂
      simp only [aboveO, POut.flow.injEq, Flow.normal.injEq] at hv
      subst hv
      rw [List.take_left' hT] at h₁
      exact ⟨o₁, h₁, by rw [List.drop_left' hT]⟩
    · obtain ⟨-, -, rfl⟩ := (hp.2 _ _ _ _ _ _ hD).1 h₂
      exact absurd trivial hnn
  · rintro ⟨o₁, h₁, rfl⟩
    refine .inl ⟨s, f, stk.take n ++ ψ (stk.drop n),
      ⟨hn, _, (hp.2 _ _ _ _ _ _ hD).2 ⟨rfl, rfl, rfl⟩, rfl⟩, ⟨by simp; omega, o₁, ?_, ?_⟩⟩
    · rwa [List.take_left' hT]
    · rw [List.drop_left' hT]

/-- **A pure morphism below commutes with a morphism on top** falling through at a fixed height. -/
theorem interchange_pure_below (hp : PureAt m m' ψ g₂) (hl : stk.length = n + m)
    (hh : ∀ s' f' vs, g₁ s f (stk.take n) s' f' (.flow (.normal vs)) → vs.length = n')
    (s' : Store H) (f' : Frame) (o : POut) :
    seqR (leftR n g₁) (rightR n' g₂) s f stk s' f' o ↔
      seqR (rightR n g₂) (leftR n g₁) s f stk s' f' o :=
  (below_lhs_iff hp hl hh).trans (below_rhs_iff hp hl).symm

end Below

/-- Typed code falls through at its target's height. -/
theorem thom_fallsAt {Γ : Ctx H} {C : Abstract.CallRel H} (hC : ArityResp Γ (fitP C))
    {I J : TIface} {es : List BExpr} (hm : THom Γ I J es) {s : Store H} {f : Frame}
    {top : List Val} (hr : Realizes Γ I s f top) (s' : Store H) (f' : Frame) (vs : List Val)
    (d : denR C es s f top s' f' (.flow (.normal vs))) : vs.length = J.ts.length := by
  obtain ⟨hg, hc⟩ := tmor_chk hm hr
  obtain ⟨-, -, -, go⟩ := evalOXP_goodO_fit hC d hg hc
  exact (Option.some.inj go).symm

theorem realizes_length {Γ : Ctx H} {I : TIface} {s : Store H} {f : Frame} {top : List Val}
    (hr : Realizes Γ I s f top) : top.length = I.ts.length := by
  have := hr.2.2.2.2.2.2.length_eq
  rwa [List.length_reverse] at this

/-- **Pure morphisms below commute with typed morphisms on top.** -/
theorem thom_interchange_pure_below {Γ : Ctx H} {C : Abstract.CallRel H}
    (hC : ArityResp Γ (fitP C)) {I J : TIface} {es : List BExpr} (hm : THom Γ I J es)
    {s : Store H} {f : Frame} {top : List Val} (hr : Realizes Γ I s f top) {m m' : Nat}
    {ψ : List Val → List Val} {g₂ : ORel H} (hp : PureAt m m' ψ g₂) (bot : List Val)
    (hb : bot.length = m) (s' : Store H) (f' : Frame) (o : POut) :
    seqR (leftR I.ts.length (denR C es)) (rightR J.ts.length g₂) s f (top ++ bot) s' f' o ↔
      seqR (rightR I.ts.length g₂) (leftR I.ts.length (denR C es)) s f (top ++ bot) s' f' o := by
  have ht := realizes_length hr
  have htake : (top ++ bot).take I.ts.length = top := by rw [← ht]; exact List.take_left' rfl
  refine interchange_pure_below hp (by simp [ht, hb]) ?_ s' f' o
  rw [htake]
  exact thom_fallsAt hC hm hr

end Silmaril.Proofs.Wasm.Abstract.TypedCatFit
