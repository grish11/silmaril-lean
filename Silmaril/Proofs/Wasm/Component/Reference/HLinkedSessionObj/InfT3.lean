module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.InfT2

/-!
# The transfer of host chatter along `Inv` (`inf_transfer`)
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

variable {X : HLinked2} {IeX IiX : SInst} {eY : Simple} {iY : SimpleI} {wY : List Nat}
  {IeY IiY : SInst} {o : GrowOracle}

theorem histStream_lt {n : Nat} {L : List (Fin n × List IVal × List IVal)}
    {ω : ℕ → Call (sigN n)} {t : ℕ} (h : t < L.length) : histStream L ω t = L[t] := by
  simp [histStream, h]

theorem histStream_ge {n : Nat} {L : List (Fin n × List IVal × List IVal)}
    {ω : ℕ → Call (sigN n)} {t : ℕ} (h : L.length ≤ t) :
    histStream L ω t = toEntry (ω (t - L.length)) := by
  simp [histStream, Nat.not_lt.2 h]

theorem streamTake_one {α : Type} (ω : ℕ → α) : streamTake ω 1 = [ω 0] := by
  simp [streamTake]

/-- **Host chatter transfers along `Inv`.** -/
theorem inf_transfer (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (hiobs : InfSame X IeX IiX eY iY wY IeY IiY len o) {sX sY : X.St}
    (hI : Inv X IeX IiX eY iY wY IeY IiY len o sX sY) {a : Nat × Payload}
    {ω : ℕ → Call (sigN X.host.length)}
    (hω : ω ∈ HLinked2.compInf (profile o) X IeX IiX sX a) :
    ω ∈ HLinked2.compInf (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY sY a := by
  obtain ⟨uX, πX, R⟩ := sX
  obtain ⟨uY, πY, R'⟩ := sY
  obtain ⟨hRR, callsX, outs, hsX, hsY, ht, hX, hY, hRX, hRY, hvX, hvY, hans⟩ := hI
  simp only at hRR hX hY hRX hRY
  subst hRR
  have hqY := LinkedSessionEquiv.typedQ_castL hty a
  cases hq : X.toL2.typedQ a with
  | none => simp [HLinked2.compInf, hq] at hω
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    rw [hq] at hqY
    simp only [Option.map_some] at hqY
    have htj := (LinkedSessionEquiv.typedQ_some hq).2
    simp only [HLinked2.compInf, hq] at hω
    obtain ⟨hC, hv⟩ := hω
    have hleg := roundInfC_legal hC hv
    have hwa : ∀ i, WellAns (ω i) := fun i => by
      obtain ⟨k, ws, us, he, -⟩ := hleg i; exact ⟨k, ws, us, he⟩
    have hlegL := answered_legal hRX hvX
    generalize hL : HLinked2.answered hsX.flatten = L at hlegL hans
    have hS : ∀ i, histStream L ω (L.length + i) = toEntry (ω i) := by
      intro i
      rw [histStream_ge (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    have hSlegal : ∀ t, ValTy.checkList X.host[(histStream L ω t).1].2.results
        (histStream L ω t).2.2 = true := by
      intro t
      rcases Nat.lt_or_ge t L.length with htl | htl
      · simp only [histStream_lt htl]
        exact hlegL _ (List.getElem_mem htl)
      · obtain ⟨k, ws, us, he, hc⟩ := hleg (t - L.length)
        simp only [histStream_ge htl, he]
        exact hc
    have hTy : X.HostTyped (scriptGS (histStream L ω)) := hostTyped_scriptGS hSlegal
    -- the histories under the stream script
    obtain ⟨R0, hR0⟩ := hv 1
    rw [streamTake_one] at hR0
    have hv0 : HLinked2.ValsCalls [ω 0] := by
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      obtain ⟨k, ws, us, he⟩ := hwa 0
      exact ⟨k, ws, by rw [he]⟩
    have pre : ∀ hs : List (List (Call (sigN X.host.length))),
        HLinked2.RealRun X.host [] hs.flatten R → HLinked2.ValsCalls hs.flatten →
        HLinked2.answered hs.flatten = L → HostRun (scriptGS (histStream L ω)) 0 hs.flatten L.length := by
      intro hs hR hvs hL
      have hRR' := realRun_append hR (visRun_realRun hR0)
      obtain ⟨-, hrun⟩ := hostRun_scriptG_prefix hRR' (valsCalls_append hvs hv0)
      rw [answered_append, hL, answered_wellAns (hwa 0)] at hrun
      refine hostRun_congr scriptG_mono hrun (fun t _ htle => scriptG_eq_scriptGS ?_)
      rcases Nat.lt_or_ge t L.length with htl | htl
      · rw [List.getElem?_append_left htl, histStream_lt htl]
        simp
      · obtain rfl : t = L.length := le_antisymm htle htl
        rw [List.getElem?_append_right (le_refl _), histStream_ge (le_refl _)]
        simp
    have hX₁ := pre hsX hRX hvX hL
    -- the chatter of `X` as a host-chatter observation
    obtain ⟨f, xs, q, c, ds, πs, N, hck, hf1, hf2, hp0, hπ0, hN0, hk, hunb⟩ := hC
    have hle : ∀ k, N k ≤ N (k + 1) := by
      intro k
      have := congrArg List.length (hk k).2.2.2
      simp [streamTake] at this
      omega
    have hsegeq : ∀ k, X.hostCalls (ds k) = (streamTake ω (N (k + 1))).drop (N k) := by
      intro k
      rw [(hk k).2.2.2, List.drop_left' (by simp [streamTake])]
    let hst : ℕ → ℕ × List HLinked2.HostEvent := fun k =>
      (L.length + N k, [] ++ evs hsX.flatten ++ evs (streamTake ω (N k)))
    have hstep : ∀ k, HostRun (HLinked2.logG (scriptGS (histStream L ω))) (hst k) (X.hostCalls (ds k)) (hst (k + 1)) := by
      intro k
      have h1 := hostRun_stream hwa hS (N k) (N (k + 1)) (hle k)
      rw [← hsegeq k] at h1
      have h2 := hostRun_logG h1 ([] ++ evs hsX.flatten ++ evs (streamTake ω (N k)))
      have h3 : [] ++ evs hsX.flatten ++ evs (streamTake ω (N k)) ++ evs (X.hostCalls (ds k)) =
          [] ++ evs hsX.flatten ++ evs (streamTake ω (N (k + 1))) := by
        rw [(hk k).2.2.2, evs_append, List.append_assoc]
      rw [h3] at h2
      exact h2
    have memX : (outs, ((L.length, [] ++ evs hsX.flatten) : ℕ × List HLinked2.HostEvent),
        fun i => evOf (ω i)) ∈ HObs (profile o) X IeX IiX callsX j vs (scriptGS (histStream L ω)) 0 := by
      refine ⟨hsX, uX, πX, hst, hX, hostRun_logG hX₁ [], ⟨f, xs, q, c, ds, πs, hck, hf1, hf2, hp0,
        hπ0, ?_, fun k => ⟨(hk k).1, (hk k).2.1, (hk k).2.2.1, hstep k⟩⟩, ?_⟩
      · simp [hst, hN0, streamTake, evs, HLinked2.answered]
      · intro N₀
        obtain ⟨k, hk'⟩ := hunb N₀
        exact ⟨N k, k, hk', by simp [hst, evs_streamTake hwa]⟩
    rw [hiobs callsX ht j vs htj (histStream L ω) hTy] at memX
    obtain ⟨hs', u', π', hstY, hYs, hR', hRI, hlogc⟩ := memX
    have hY₁ := pre hsY hRY hvY hans.symm
    obtain ⟨hRs', -⟩ := hostRun_of_logG hR'
    obtain ⟨-, rfl, rfl, rfl, -⟩ := sess_unique _ _ hY hY₁ hYs hRs'
    -- the chatter of `Y` is `ω`
    obtain ⟨f', xs', q', c', ds', πs', hck', hf1', hf2', hp0', hπ0', hst0', hk'⟩ := hRI
    have hnr := seg_no_refuse (l := ⟨eY, iY, wY, X.host⟩)
      (fun k => ⟨(hk' k).1, (hk' k).2.1⟩)
    let N' : ℕ → ℕ := fun k => (hstY k).1 - L.length
    let Q : ℕ → Prop := fun k => (hstY k).1 = L.length + N' k ∧
      (hstY k).2 = [] ++ evs hsX.flatten ++ evs (streamTake ω (N' k))
    have step : ∀ k, Q k → Q (k + 1) ∧
        streamTake ω (N' (k + 1)) = streamTake ω (N' k) ++
          (⟨eY, iY, wY, X.host⟩ : HLinked2).hostCalls (ds' k) := by
      rintro k ⟨hq1, hq2⟩
      obtain ⟨hrun, hlog⟩ := hostRun_of_logG (hk' k).2.2.2
      rw [hq1] at hrun
      obtain ⟨ht1, hseg⟩ := seg_of_run hwa hS _ (N' k) _ hrun (hnr k)
      have hN : N' (k + 1) = N' k + ((⟨eY, iY, wY, X.host⟩ : HLinked2).hostCalls (ds' k)).length := by
        simp only [N', ht1]; omega
      have hsplit : streamTake ω (N' (k + 1)) = streamTake ω (N' k) ++
          (⟨eY, iY, wY, X.host⟩ : HLinked2).hostCalls (ds' k) := by
        rw [hN, streamTake_split ω (a := N' k) (Nat.le_add_right _ _)]
        congr 1
        exact hseg.symm
      refine ⟨⟨by simp only [N', ht1]; omega, ?_⟩, hsplit⟩
      rw [hlog, hq2, hsplit, evs_append, List.append_assoc]
    have hQ : ∀ k, Q k := by
      intro k
      induction k with
      | zero =>
        show (hstY 0).1 = L.length + ((hstY 0).1 - L.length) ∧
          (hstY 0).2 = [] ++ evs hsX.flatten ++ evs (streamTake ω ((hstY 0).1 - L.length))
        rw [hst0']
        simp [streamTake, evs, HLinked2.answered]
      | succ k ih => exact (step k ih).1
    simp only [HLinked2.compInf, hqY]
    refine ⟨⟨f', xs', q', c', ds', πs', N', hck', hf1', hf2', hp0', hπ0', ?_,
      fun k => ⟨(hk' k).1, (hk' k).2.1, (hk' k).2.2.1, (step k (hQ k)).2⟩, ?_⟩, hv⟩
    · simp [N', hst0']
    · intro N₀
      obtain ⟨n, k, hn, he⟩ := hlogc N₀
      refine ⟨k, ?_⟩
      have h2 := (hQ k).2
      rw [he] at h2
      have h3 : streamTake (fun i => evOf (ω i)) n = streamTake (fun i => evOf (ω i)) (N' k) := by
        rw [← evs_streamTake hwa (N' k)]
        simpa using h2
      have := congrArg List.length h3
      simp [streamTake] at this
      omega

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
