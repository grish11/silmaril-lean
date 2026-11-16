module

public import Silmaril.Proofs.Wasm.Component.DWiringLaws.Basic

/-!
# Wiring handlers make at most one call

A chain of adapters transforms the argument and the result of a single target
call (`runChain`), so `implsH`, `implsN` (hence `exportsH`) and `maskH` are
one-call handlers.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DWiringLaws

open Silmaril.Games Silmaril.Wasm.Component

/-- A program making at most one call. -/
def OneProg {E : Sig.{0}} {A : Type} (c : Prog E A) : Prop :=
  (∃ r, c = .pure r) ∨ ∃ m k, c = .call m k ∧ ∀ n, ∃ r, k n = .pure r

theorem oneProg_bind_pure {E : Sig.{0}} {A B : Type} {c : Prog E A} (hc : OneProg c)
    (f : A → B) : OneProg (c.bind fun a => .pure (f a)) := by
  rcases hc with ⟨r, rfl⟩ | ⟨m, k, rfl, hk⟩
  · exact .inl ⟨f r, rfl⟩
  · refine .inr ⟨m, _, rfl, fun n => ?_⟩
    obtain ⟨r, hr⟩ := hk n
    exact ⟨f r, by rw [hr]; rfl⟩

theorem oneProg_runChain {E : Sig.{0}} : ∀ (c : List Adapter)
    (k : Payload → Prog E (Option Payload)), (∀ a, OneProg (k a)) →
      ∀ a, OneProg (runChain c k a)
  | [], _, hk, a => hk a
  | ad :: c, k, hk, a => by
    unfold runChain
    split
    · exact .inl ⟨none, rfl⟩
    · exact oneProg_bind_pure (oneProg_runChain c k hk _) _

theorem oneProg_target (e : Nat) (t : Target) (a : Payload) : OneProg (t.prog e a) := by
  cases t with
  | call r =>
    by_cases hr : r < e
    · rw [show Target.prog e (.call r) a = .call (r, a) (fun n => .pure n) by
        simp [Target.prog, hr]]
      exact .inr ⟨_, _, rfl, fun n => ⟨n, rfl⟩⟩
    · rw [show Target.prog e (.call r) a = .pure none by simp [Target.prog, hr]]
      exact .inl ⟨none, rfl⟩
  | const res => exact .inl ⟨res, rfl⟩

theorem oneCall_implsH (e : Nat) (ims : List Impl) : OneCall (implsH e ims) := by
  intro q
  unfold implsH
  split
  · exact oneProg_runChain _ _ (oneProg_target e _) _
  · exact .inl ⟨none, rfl⟩

theorem oneCall_implsN (e : Nat) (ims : List Impl) (t : Nat) : OneCall (implsN e ims t) :=
  fun q => oneCall_implsH e ims (q.1.val, q.2)

theorem oneCall_maskH (e : Nat) : OneCall (maskH e) :=
  fun q => oneProg_target e (.call q.1) q.2

end Silmaril.Proofs.Wasm.Component.DWiringLaws
