module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Probe
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionEquiv.Main
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.IR

/-!
# Transferring finished rounds between linked components with the same observations

`Inv` relates a state of the triple of `X` and one of `Y` (with the host imports of `X`) reached by
specification sessions of the same calls and outcomes whose host calls are realizable histories
with the same answered calls and the same refusals since the last answer. If `X` and `Y` have the
same finite observations under every scripted host (`SObs`), then every finished behaviour of `X`
at `Inv`-related states is one of `Y`, with `Inv`-related end states (`ret_transfer`): the
scripted host of the history and the round makes `Y`'s session unique; its visible calls are
those of `X`'s round, the refusals being matched by `probe`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Component.Runtime (HostFuncId)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Shapes of rounds -/

theorem realRun_split {h : Iface} :
    ∀ {R R₂ : List (sigN h.length).Op} {A B : List (Call (sigN h.length))},
      HLinked2.RealRun h R (A ++ B) R₂ →
      ∃ R₁, HLinked2.RealRun h R A R₁ ∧ HLinked2.RealRun h R₁ B R₂
  | R, _, [], _, hr => ⟨R, .nil R, hr⟩
  | _, _, _ :: A, _, hr => by
    cases hr with
    | forced hF hr =>
      obtain ⟨R₁, h₁, h₂⟩ := realRun_split hr
      exact ⟨R₁, .forced hF h₁, h₂⟩
    | refuse hF hr =>
      obtain ⟨R₁, h₁, h₂⟩ := realRun_split hr
      exact ⟨R₁, .refuse hF h₁, h₂⟩
    | answer hm hl hr =>
      obtain ⟨R₁, h₁, h₂⟩ := realRun_split hr
      exact ⟨R₁, .answer hm hl h₁, h₂⟩

theorem realRun_det {h : Iface} {R R₁ R₂ : List (sigN h.length).Op}
    {c : List (Call (sigN h.length))} (h₁ : HLinked2.RealRun h R c R₁)
    (h₂ : HLinked2.RealRun h R c R₂) : R₁ = R₂ := by
  induction h₁ generalizing R₂ with
  | nil => cases h₂; rfl
  | forced hF _ ih =>
    cases h₂ with
    | forced _ h => exact ih h
    | refuse hF' _ => exact (hF' hF).elim
  | refuse hF _ ih =>
    cases h₂ with
    | forced hF' _ => exact (hF hF').elim
    | refuse _ h => exact ih h
  | answer _ _ _ ih => cases h₂ with | answer _ _ h => exact ih h

/-- Every call answered, on IR values. -/
def AllAns {n : Nat} (A : List (Call (sigN n))) : Prop :=
  ∀ x ∈ A, ∃ (k : Fin n) (ws us : List IVal), x = ⟨(k, .vals ws), some (.vals us)⟩

theorem allAns_eq {n : Nat} :
    ∀ {A B : List (Call (sigN n))}, AllAns A → AllAns B →
      HLinked2.answered A = HLinked2.answered B → A = B
  | [], [], _, _, _ => rfl
  | [], b :: B, _, hB, h => by
    obtain ⟨k, ws, us, rfl⟩ := hB b (by simp)
    simp [HLinked2.answered] at h
  | a :: A, [], hA, _, h => by
    obtain ⟨k, ws, us, rfl⟩ := hA a (by simp)
    simp [HLinked2.answered] at h
  | a :: A, b :: B, hA, hB, h => by
    obtain ⟨k, ws, us, rfl⟩ := hA a (by simp)
    obtain ⟨k', ws', us', rfl⟩ := hB b (by simp)
    rw [answered_cons_vals, answered_cons_vals] at h
    simp only [List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, h⟩ := h
    rw [allAns_eq (fun x hx => hA x (by simp [hx])) (fun x hx => hB x (by simp [hx])) h]

theorem hostRun_forms {τ : Type} {g : τ → HostFuncId → List RVal → Option (List RVal × τ)}
    {n : Nat} {s s' : τ} {H : List (Call (sigN n))} (h : HostRun g s H s') :
    ∀ x ∈ H, x.2 = none ∨ ∃ (k : Fin n) (ws us : List IVal), x = ⟨(k, .vals ws), some (.vals us)⟩ := by
  induction h with
  | nil => intro x hx; cases hx
  | cons hd _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨m, R⟩ := x
      obtain ⟨k, ws, hm, hA⟩ := hd
      simp only at hm hA
      subst hm
      rcases R with _ | ⟨fs | us⟩
      · exact .inl rfl
      · exact hA.elim
      · exact .inr ⟨k, ws, us, rfl⟩
    · exact ih x hx

variable {l : HLinked2} {Ie Ii : SInst}

/-- **The shape of a round under a host**: answered calls, then at most one refusal. -/
theorem round_shape {P : Profile} {u π u' π' : Store Nat} {q : Fin l.imp.exports.length × List IVal}
    {o : Option (List IVal)} {H : List (Call (sigN l.host.length))}
    (r : HLinked2.SessSpec P l Ie Ii u π [q] [o] [H] u' π')
    (hforms : ∀ x ∈ H, x.2 = none ∨
      ∃ (k : Fin l.host.length) (ws us : List IVal), x = ⟨(k, .vals ws), some (.vals us)⟩) :
    ∃ A T, H = A ++ T ∧ AllAns A ∧ (T = [] ∨ ∃ m, T = [⟨m, none⟩]) := by
  by_cases hn : ∃ x ∈ H, x.2 = none
  · obtain ⟨⟨m, R⟩, hx, hxn⟩ := hn
    simp only at hxn
    subst hxn
    obtain ⟨H₁, H₂, rfl⟩ := List.append_of_mem hx
    obtain ⟨rfl, -⟩ := refuse_last r rfl
    refine ⟨H₁, [⟨m, none⟩], rfl, fun y hy => ?_, .inr ⟨m, rfl⟩⟩
    rcases hforms y (by simp [hy]) with hy' | hy'
    · exfalso
      obtain ⟨y1, y2⟩ := y
      simp only at hy'
      subst hy'
      obtain ⟨B₁, B₂, rfl⟩ := List.append_of_mem hy
      have := (refuse_last r (H₁ := B₁) (H₂ := B₂ ++ [⟨m, none⟩]) (m := y1) (by simp)).1
      simp at this
    · exact hy'
  · simp only [not_exists, not_and] at hn
    refine ⟨H, [], by simp, fun y hy => ?_, .inl rfl⟩
    rcases hforms y hy with hy' | hy'
    · exact (hn y hy hy').elim
    · exact hy'

theorem answered_allAns_append {n : Nat} {A T : List (Call (sigN n))}
    (hT : T = [] ∨ ∃ m, T = [⟨m, none⟩]) : HLinked2.answered (A ++ T) = HLinked2.answered A := by
  rcases hT with rfl | ⟨m, rfl⟩
  · simp
  · rw [answered_append, answered_cons_none]; simp [HLinked2.answered]

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
