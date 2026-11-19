module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.DivT
public import Silmaril.Games.Abstract.SessionLegal.Thms

/-!
# The transfer of host chatter

Host chatter answers every host call (`roundInfC_no_refuse`, and `seg_no_refuse` for
`RoundInf`), so the host-chatter observations under the stream script of the history followed
by the chatter (`scriptGS`) determine it (`inf_transfer`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile Thread)
open Silmaril.Wasm.Component.Runtime (HostFuncId)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Stream scripts -/

/-- **The stream script**: in state `i` it answers exactly the `i`-th scripted call. -/
def scriptGS {n : Nat} (S : ℕ → Fin n × List IVal × List IVal) :
    ℕ → HostFuncId → List RVal → Option (List RVal × ℕ) :=
  fun i fn args =>
    if fn = ⟨(S i).1.val⟩ ∧ args = (S i).2.1.map toRefVal then some ((S i).2.2.map toRefVal, i + 1)
    else none

/-- The entry of an answered call. -/
def toEntry {n : Nat} : Call (sigN n) → Fin n × List IVal × List IVal
  | ⟨(k, .vals ws), some (.vals us)⟩ => (k, ws, us)
  | ⟨(k, _), _⟩ => (k, [], [])

/-- The history `L` of answered calls, then the stream `ω`. -/
def histStream {n : Nat} (L : List (Fin n × List IVal × List IVal)) (ω : ℕ → Call (sigN n)) :
    ℕ → Fin n × List IVal × List IVal :=
  fun i => if h : i < L.length then L[i] else toEntry (ω (i - L.length))

theorem hostRun_counter_le {g : ℕ → HostFuncId → List RVal → Option (List RVal × ℕ)}
    (hmono : ∀ i fn args r j, g i fn args = some (r, j) → j = i + 1) {n : Nat} {s s' : ℕ}
    {H : List (Call (sigN n))} (h : HostRun g s H s') : s ≤ s' := by
  induction h with
  | nil => exact le_rfl
  | @cons s s₁ s₂ d ds hd _ ih =>
    obtain ⟨m, R⟩ := d
    obtain ⟨k, ws, -, hA⟩ := hd
    rcases R with _ | ⟨fs | us⟩
    · obtain ⟨-, rfl⟩ := hA; exact ih
    · exact hA.elim
    · have := hmono _ _ _ _ _ hA; omega

theorem hostRun_congr {g₁ g₂ : ℕ → HostFuncId → List RVal → Option (List RVal × ℕ)}
    (hmono : ∀ i fn args r j, g₁ i fn args = some (r, j) → j = i + 1) {n : Nat} {s s' : ℕ}
    {H : List (Call (sigN n))} (h : HostRun g₁ s H s') (hag : ∀ t, s ≤ t → t ≤ s' → g₁ t = g₂ t) :
    HostRun g₂ s H s' := by
  induction h with
  | nil => exact .nil _
  | @cons s s₁ s₂ d ds hd hr ih =>
    have h₁ := hostRun_counter_le hmono hr
    have h₀ : s ≤ s₁ := by
      obtain ⟨m, R⟩ := d
      obtain ⟨k, ws, -, hA⟩ := hd
      rcases R with _ | ⟨fs | us⟩
      · obtain ⟨-, rfl⟩ := hA; exact le_rfl
      · exact hA.elim
      · have := hmono _ _ _ _ _ hA; omega
    have hs : g₁ s = g₂ s := hag s le_rfl (h₀.trans h₁)
    refine .cons ?_ (ih fun t ht ht' => hag t (h₀.trans ht) ht')
    obtain ⟨m, R⟩ := d
    obtain ⟨k, ws, hm, hA⟩ := hd
    exact ⟨k, ws, hm, by rw [← hs]; exact hA⟩

theorem scriptG_mono {n : Nat} {S : List (Fin n × List IVal × List IVal)} :
    ∀ i fn args r j, HLinked2.scriptG S i fn args = some (r, j) → j = i + 1 := by
  intro i fn args r j h
  simp only [HLinked2.scriptG] at h
  split at h
  · split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · cases h

theorem scriptG_eq_scriptGS {n : Nat} {L : List (Fin n × List IVal × List IVal)}
    {S : ℕ → Fin n × List IVal × List IVal} {t : ℕ} (h : L[t]? = some (S t)) :
    HLinked2.scriptG L t = scriptGS S t := by
  funext fn args
  simp [HLinked2.scriptG, scriptGS, h]

/-- An answered call, on IR values. -/
def WellAns {n : Nat} (x : Call (sigN n)) : Prop :=
  ∃ (k : Fin n) (ws us : List IVal), x = ⟨(k, .vals ws), some (.vals us)⟩

theorem answered_wellAns {n : Nat} {x : Call (sigN n)} (h : WellAns x) :
    HLinked2.answered [x] = [toEntry x] := by
  obtain ⟨k, ws, us, rfl⟩ := h; rfl

theorem scriptGS_answers {n : Nat} {S : ℕ → Fin n × List IVal × List IVal} {t : ℕ}
    {x : Call (sigN n)} (hx : WellAns x) (hS : S t = toEntry x) :
    HostAnswersS (scriptGS S) t x (t + 1) := by
  obtain ⟨k, ws, us, rfl⟩ := hx
  refine ⟨k, ws, rfl, ?_⟩
  simp [scriptGS, hS, toEntry]

theorem hostRun_stream {n : Nat} {S : ℕ → Fin n × List IVal × List IVal} {ω : ℕ → Call (sigN n)}
    {n₁ : ℕ} (hω : ∀ i, WellAns (ω i)) (hS : ∀ i, S (n₁ + i) = toEntry (ω i)) :
    ∀ (a b : ℕ), a ≤ b → HostRun (scriptGS S) (n₁ + a) ((streamTake ω b).drop a) (n₁ + b)
  | a, 0, h => by
    obtain rfl : a = 0 := by omega
    simpa [streamTake] using HostRun.nil (g := scriptGS S) (n₁ + 0)
  | a, b + 1, h => by
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · rw [SessionLegal.streamTake_succ, List.drop_append_of_le_length (by simp [streamTake]; omega)]
      refine hostRun_append.2 ⟨n₁ + b, hostRun_stream hω hS a b (by omega), ?_⟩
      exact .cons (scriptGS_answers (hω b) (hS b)) (by rw [Nat.add_assoc]; exact .nil _)
    · obtain rfl : a = b + 1 := by omega
      rw [List.drop_of_length_le (by simp [streamTake])]
      exact .nil _

/-- The calls a stream script answers along a run without refusals are the stream's. -/
theorem seg_of_run {n : Nat} {S : ℕ → Fin n × List IVal × List IVal} {ω : ℕ → Call (sigN n)}
    {n₁ : ℕ} (hω : ∀ i, WellAns (ω i)) (hS : ∀ i, S (n₁ + i) = toEntry (ω i)) :
    ∀ (seg : List (Call (sigN n))) (a t : ℕ), HostRun (scriptGS S) (n₁ + a) seg t →
      (∀ x ∈ seg, x.2 ≠ none) →
      t = n₁ + (a + seg.length) ∧ seg = (streamTake ω (a + seg.length)).drop a
  | [], a, t, h, _ => by
    cases h
    simp [streamTake]
  | x :: seg, a, t, h, hn => by
    cases h with
    | cons hd hr =>
      obtain ⟨m, R⟩ := x
      obtain ⟨k, ws, hm, hA⟩ := hd
      simp only at hm hA
      subst hm
      rcases R with _ | ⟨fs | us⟩
      · exact (hn _ List.mem_cons_self rfl).elim
      · exact hA.elim
      · simp only [scriptGS, hS] at hA
        split_ifs at hA with hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hA
        obtain ⟨hu, rfl⟩ := hA
        obtain ⟨k', ws', us', hω'⟩ := hω a
        rw [hω'] at hc hu
        simp only [toEntry, HostFuncId.mk.injEq] at hc hu
        obtain ⟨hk, hw⟩ := hc
        have hk' : k = k' := Fin.ext hk
        subst hk'
        obtain rfl := map_toRefVal_inj hw
        obtain rfl := map_toRefVal_inj hu
        obtain ⟨ht, hseg⟩ := seg_of_run hω hS seg (a + 1) t (by rw [← Nat.add_assoc]; exact hr)
          (fun y hy => hn y (by simp [hy]))
        refine ⟨by simp only [List.length_cons] at *; omega, ?_⟩
        simp only [List.length_cons]
        rw [show a + (seg.length + 1) = a + 1 + seg.length by omega]
        have hlen : a < (streamTake ω (a + 1 + seg.length)).length := by
          simp [streamTake]; omega
        rw [List.drop_eq_getElem_cons hlen, ← hseg]
        simp [streamTake, hω']

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
