module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.InfT

/-!
# The transfer of host chatter: the transfer

`HObs` (the host-chatter observations at fixed instances), `InfSame`, `inf_transfer`.
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

variable {l : HLinked2} {Ie Ii : SInst}

/-- Host chatter answers every host call (the form of `RoundInf` and `RoundInfC`). -/
theorem seg_no_refuse {P : Profile} {q : ℕ → Ii.HState} {c : ℕ → Σ e : Ii.E.Op, Ii.E.Ar e}
    {ds : ℕ → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
    (hk : ∀ k, Ii.Path P (q k) (Silmaril.Wasm.Component.Reference.callMoves [c k]) (q (k + 1)) ∧
      Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii (c k) (ds k)) (k : ℕ) :
    ∀ x ∈ l.hostCalls (ds k), x.2 ≠ none := by
  intro x hx hxn
  obtain ⟨hp, hd⟩ := hk k
  rcases impRel_hostCalls hd with hn | ⟨y, hy, htr⟩
  · rw [hn] at hx; cases hx
  · rw [hy, List.mem_singleton] at hx
    subst hx
    have htrap := htr hxn
    have hp' := (hk (k + 1)).1
    generalize c k = ck at hp htrap
    generalize c (k + 1) = ck' at hp'
    generalize q (k + 1 + 1) = q2 at hp'
    generalize q (k + 1) = q1 at hp hp'
    generalize q k = q0 at hp
    obtain ⟨e, n⟩ := ck
    simp only at htrap
    subst htrap
    simp only [Silmaril.Wasm.Component.Reference.callMoves] at hp
    cases hp with
    | cons h₁ hp =>
      cases h₁ with
      | ucall run callout op =>
        cases hp with
        | cons h₂ hp =>
          cases h₂ with
          | uret _ =>
            cases hp
            have ht := trapped_resume callout
            obtain ⟨e', n'⟩ := ck'
            simp only [Silmaril.Wasm.Component.Reference.callMoves] at hp'
            cases path_trapped ht hp'

theorem streamTake_take {α : Type} (ω : ℕ → α) {a m : ℕ} (h : a ≤ m) :
    (streamTake ω m).take a = streamTake ω a := by
  apply List.ext_getElem
  · simp [streamTake]; omega
  · intro i h₁ h₂
    simp [streamTake]

theorem streamTake_split {α : Type} (ω : ℕ → α) {a m : ℕ} (h : a ≤ m) :
    streamTake ω m = streamTake ω a ++ (streamTake ω m).drop a := by
  rw [← streamTake_take ω h, List.take_append_drop]

/-- Legally answered on IR values. -/
def LegalAns (h : Iface) (x : Call (sigN h.length)) : Prop :=
  ∃ (k : Fin h.length) (ws us : List IVal), x = ⟨(k, .vals ws), some (.vals us)⟩ ∧
    ValTy.checkList h[k].2.results us = true

theorem roundInfC_legal {P : Profile} {u π : Store Nat} {j : Fin l.imp.exports.length}
    {vs : List IVal} {ω : ℕ → Call (sigN l.host.length)} {R : List (sigN l.host.length).Op}
    (h : HLinked2.RoundInfC P l Ie Ii u π j vs ω)
    (hv : ∀ n, ∃ R', HLinked2.VisRun l.host R (streamTake ω n) R') (i : ℕ) :
    LegalAns l.host (ω i) := by
  have hnr := roundInfC_no_refuse h i
  obtain ⟨f, xs, q, c, ds, πs, N, -, -, -, -, -, hN0, hk, hunb⟩ := h
  have hval : ∀ k, HLinked2.ValsCalls (streamTake ω (N k)) := by
    intro k
    induction k with
    | zero => rw [hN0]; intro x hx; simp [streamTake] at hx
    | succ k ih =>
      rw [(hk k).2.2.2]
      exact valsCalls_append ih (valsCalls_impRel (hk k).2.1)
  obtain ⟨k, hk'⟩ := hunb (i + 1)
  obtain ⟨kk, ws, hop⟩ := hval k (ω i) (List.mem_ofFn.2 ⟨⟨i, by omega⟩, rfl⟩)
  obtain ⟨R', hR'⟩ := hv (i + 1)
  rw [SessionLegal.streamTake_succ] at hR'
  obtain ⟨R₁, -, hR₂⟩ := visRun_split hR'
  generalize ω i = x at hop hnr hR₂ ⊢
  obtain ⟨m, r⟩ := x
  simp only at hop hnr
  subst hop
  rcases r with _ | ⟨fs | us⟩
  · exact (hnr rfl).elim
  · cases hR₂ with | answer _ hl _ => exact hl.elim
  · cases hR₂ with | answer _ hl _ => exact ⟨kk, ws, us, rfl, hl⟩

/-- **The host-chatter observations** at fixed instances. -/
def HObs (P : Profile) (l : HLinked2) (Ie Ii : SInst)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) {τ : Type} (g : τ → HostFuncId → List RVal → Option (List RVal × τ))
    (s₀ : τ) : Set (List (Option (List IVal)) × (τ × List HLinked2.HostEvent) × (ℕ → HLinked2.HostEvent)) :=
  {p | ∃ hs u π, ∃ hst : ℕ → τ × List HLinked2.HostEvent,
    HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls p.1 hs u π ∧
    HostRun (HLinked2.logG g) (s₀, []) hs.flatten p.2.1 ∧
    HLinked2.RoundInf P l Ie Ii (HLinked2.logG g) u π p.2.1 j vs hst ∧
    ∀ N, ∃ n k, N ≤ n ∧ (hst k).2 = p.2.1.2 ++ streamTake p.2.2 n}

/-- The same host-chatter observations under every stream script. -/
def InfSame (X : HLinked2) (IeX IiX : SInst) (eY : Simple) (iY : SimpleI) (wY : List Nat)
    (IeY IiY : SInst) (len : X.imp.exports.length = iY.exports.length) (o : GrowOracle) : Prop :=
  ∀ callsX : List (Fin X.imp.exports.length × List IVal), SimpleI.TypedCalls X.imp callsX →
    ∀ (j : Fin X.imp.exports.length) (vs : List IVal),
      ValTy.checkList X.imp.exports[j].ty.params vs = true →
    ∀ S : ℕ → Fin X.host.length × List IVal × List IVal, X.HostTyped (scriptGS S) →
      HObs (profile o) X IeX IiX callsX j vs (scriptGS S) 0 =
        HObs (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY
          (Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len callsX) (Fin.cast len j) vs
          (scriptGS S) 0

/-- The log entry of an answered call. -/
def evOf {n : Nat} (x : Call (sigN n)) : HLinked2.HostEvent :=
  (⟨(toEntry x).1.val⟩, (toEntry x).2.1.map toRefVal, (toEntry x).2.2.map toRefVal)

theorem evs_streamTake {n : Nat} {ω : ℕ → Call (sigN n)} (hω : ∀ i, WellAns (ω i)) :
    ∀ m, evs (streamTake ω m) = streamTake (fun i => evOf (ω i)) m
  | 0 => by simp [evs, streamTake, HLinked2.answered]
  | m + 1 => by
    rw [SessionLegal.streamTake_succ, SessionLegal.streamTake_succ, evs_append,
      evs_streamTake hω m]
    obtain ⟨k, ws, us, he⟩ := hω m
    simp [evs, he, evOf, toEntry, HLinked2.answered]

theorem hostTyped_scriptGS {S : ℕ → Fin l.host.length × List IVal × List IVal}
    (hS : ∀ t, ValTy.checkList l.host[(S t).1].2.results (S t).2.2 = true) :
    l.HostTyped (scriptGS S) := by
  intro i k hk ws rs s' h
  simp only [scriptGS] at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  obtain ⟨hf, -⟩ := hc
  have hk' : k = (S i).1.val := by simpa using congrArg HostFuncId.idx hf
  subst hk'
  exact ⟨_, rfl, by simpa using hS i⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
