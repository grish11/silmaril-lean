module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.BackObs
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Sess

/-!
# Host chatter read back along a bisimulation

The host calls of the rounds of `HLinked2.RoundInf` under a typed host are flattened into one
stream `ω` (`flatSeg`, `flatStream`): the logs are unboundedly long, so are the flattened
prefixes. The stream is a productive stream of the triple, which the bisimulation transfers, and
it is read back as a `RoundInf` of the other component under the same host
(`sessHProds_sub`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (IsBisim ObsEq RoundEq)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile Thread)
open Silmaril.Wasm.Component.Runtime (HostFuncId)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Flattening segments -/

section Flat

variable {α : Type} (seg : ℕ → List α)

/-- The first `k` segments, concatenated. -/
def flatSeg : ℕ → List α
  | 0 => []
  | k + 1 => flatSeg k ++ seg k

theorem flatSeg_prefix : ∀ {k k' : ℕ}, k ≤ k' → flatSeg seg k <+: flatSeg seg k'
  | k, k', h => by
    induction h with
    | refl => exact List.prefix_refl _
    | step _ ih => exact ih.trans (List.prefix_append _ _)

theorem flatSeg_mono {k k' : ℕ} (h : k ≤ k') : (flatSeg seg k).length ≤ (flatSeg seg k').length :=
  (flatSeg_prefix seg h).length_le

variable {seg}

open Classical in
/-- **The stream of the segments**, when their lengths are unbounded. -/
noncomputable def flatStream (hu : ∀ n, ∃ k, n < (flatSeg seg k).length) (i : ℕ) : α :=
  (flatSeg seg (Nat.find (hu i)))[i]'(Nat.find_spec (hu i))

theorem flatSeg_getElem {k : ℕ} {i : ℕ} (hi : i < (flatSeg seg k).length) {k' : ℕ}
    (hi' : i < (flatSeg seg k').length) : (flatSeg seg k)[i] = (flatSeg seg k')[i] := by
  rcases le_total k k' with h | h
  · exact (flatSeg_prefix seg h).getElem hi
  · exact ((flatSeg_prefix seg h).getElem hi').symm

theorem flatSeg_eq_streamTake (hu : ∀ n, ∃ k, n < (flatSeg seg k).length) (k : ℕ) :
    flatSeg seg k = streamTake (flatStream hu) (flatSeg seg k).length := by
  apply List.ext_getElem
  · simp [streamTake]
  · intro i h₁ h₂
    simp only [streamTake, List.getElem_ofFn, flatStream]
    exact flatSeg_getElem h₁ _

end Flat

/-! ## The read-back of host chatter -/

variable {X : HLinked2} {IeX IiX : SInst} {eY : Simple} {iY : SimpleI} {wY : List Nat}
  {IeY IiY : SInst} {o : GrowOracle}

theorem allAns_evs_length {n : Nat} {A : List (Call (sigN n))} (h : AllAns A) :
    (evs A).length = A.length := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    obtain ⟨k, ws, us, rfl⟩ := h x List.mem_cons_self
    have : evs (⟨(k, .vals ws), some (.vals us)⟩ :: A) =
        (⟨k.val⟩, ws.map toRefVal, us.map toRefVal) :: evs A := rfl
    rw [this, List.length_cons, List.length_cons, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem allAns_append {n : Nat} {A B : List (Call (sigN n))} (hA : AllAns A) (hB : AllAns B) :
    AllAns (A ++ B) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hA x hx
  · exact hB x hx

theorem streamTake_eq_take {α : Type} (ω : ℕ → α) {m M : ℕ} (h : m ≤ M) :
    streamTake ω m = (streamTake ω M).take m :=
  (streamTake_take ω h).symm

/-- **The host chatter transfers along a bisimulation of the initial states.** -/
theorem sessHProds_sub (hIe : X.exp.mod.IsInst IeX) (hIi : X.imp.mod.IsInst IiX)
    (hIe' : eY.mod.IsInst IeY) (hIi' : iY.mod.IsInst IiY) {Rel : X.St → X.St → Prop}
    (hB : IsBisim (HLinked2.compTripleS (profile o) X IeX IiX)
      (HLinked2.compTripleS (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY) Rel)
    (h0 : Rel (IiX.store, IeX.store, []) (IiY.store, IeY.store, []))
    (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (calls : List (Fin X.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls X.imp calls)
    (j : Fin X.imp.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList X.imp.exports[j].ty.params vs = true)
    {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (hT : X.HostTyped g)
    (s₀ : σ) :
    HLinked2.sessHProds (profile o) X g s₀ calls j vs ⊆
      HLinked2.sessHProds (profile o) ⟨eY, iY, wY, X.host⟩ g s₀
        (Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len calls) (Fin.cast len j) vs := by
  rintro ⟨outs, st, ev⟩ ⟨Ie₀, Ii₀, hs, u, π, hst, hIe₀, hIi₀, hS, hr, hRI, hlogc⟩
  have e1 : IeX = Ie₀ := NumModule.IsInst.unique hIe hIe₀
  have e2 : IiX = Ii₀ := ImpModule.IsInst.unique hIi hIi₀
  subst e1 e2
  have hTG := HLinkedSession.HostTyped.logG hT
  set G := HLinked2.logG g with hG
  obtain ⟨R, u', π', hs', hRel, hRef, hS', hr'⟩ :=
    sess_back hTG hB len hty calls h0 (fun _ h => (List.not_mem_nil h).elim) ht hS hr
  obtain ⟨f, xs, q, c, ds, πs, hck, hf1, hf2, hp0, hπ0, hst0, hk⟩ := hRI
  -- the segments and their flattening
  let seg : ℕ → List (Call (sigN X.host.length)) := fun k => X.hostCalls (ds k)
  have hsegA : ∀ k, AllAns (seg k) := fun k =>
    allAns_of_hostRun (hk k).2.2.2 (seg_no_refuse (fun k => ⟨(hk k).1, (hk k).2.1⟩) k)
  have hflatA : ∀ k, AllAns (flatSeg seg k) := by
    intro k
    induction k with
    | zero => intro x hx; cases hx
    | succ k ih => exact allAns_append ih (hsegA k)
  have hflatR : ∀ k, HostRun G st (flatSeg seg k) (hst k) := by
    intro k
    induction k with
    | zero => rw [hst0]; exact .nil _
    | succ k ih => exact hostRun_append.2 ⟨hst k, ih, (hk k).2.2.2⟩
  have hflatL : ∀ k, (hst k).2 = st.2 ++ evs (flatSeg seg k) := fun k =>
    (hostRun_of_logG (hflatR k)).2
  have hu : ∀ n, ∃ k, n < (flatSeg seg k).length := by
    intro n
    obtain ⟨n', k, hn, he⟩ := hlogc (n + 1)
    refine ⟨k, ?_⟩
    have := congrArg List.length (he.symm.trans (hflatL k))
    simp only [List.length_append, add_right_inj] at this
    rw [allAns_evs_length (hflatA k)] at this
    simp [streamTake] at this
    omega
  let ω := flatStream hu
  have hflat : ∀ k, flatSeg seg k = streamTake ω (flatSeg seg k).length :=
    flatSeg_eq_streamTake hu
  have hωA : ∀ i, WellAns (ω i) := by
    intro i
    obtain ⟨k, hk'⟩ := hu i
    have hmem : ω i ∈ flatSeg seg k := by
      rw [hflat k]; exact List.mem_ofFn.2 ⟨⟨i, hk'⟩, rfl⟩
    exact hflatA k _ hmem
  -- the prefixes of the stream are host runs
  have hpre : ∀ m, ∃ t, HostRun G st (streamTake ω m) t := by
    intro m
    obtain ⟨k, hk'⟩ := hu m
    have h := hflatR k
    rw [hflat k, streamTake_split ω (a := m) (m := (flatSeg seg k).length) (by omega)] at h
    obtain ⟨t, h₁, -⟩ := hostRun_append.1 h
    exact ⟨t, h₁⟩
  have hvis : ∀ n, ∃ R', HLinked2.VisRun X.host R (streamTake ω n) R' := by
    intro n
    obtain ⟨t, h⟩ := hpre n
    obtain ⟨R', hR', -⟩ := realRun_of_hostRun_aux _ hTG h R hRef
    exact ⟨R', realRun_vis (fun x hx => by
      obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_ofFn.1 hx; exact hωA i) hR'⟩
  -- the logs of the stream's prefixes
  have hev : ∀ m, evs (streamTake ω m) = streamTake ev m := by
    intro m
    obtain ⟨n', k, hn, he⟩ := hlogc m
    have h1 : evs (flatSeg seg k) = streamTake ev n' := by
      have := he.symm.trans (hflatL k)
      exact (List.append_cancel_left this).symm
    have hlen : n' = (flatSeg seg k).length := by
      have := congrArg List.length h1
      rw [allAns_evs_length (hflatA k)] at this
      simp [streamTake] at this; omega
    have hmk : m ≤ (flatSeg seg k).length := by omega
    rw [hflat k] at h1
    rw [streamTake_eq_take ev (hlen ▸ hmk : m ≤ n'), ← h1, streamTake_split ω hmk, evs_append]
    have hE : (evs (streamTake ω m)).length = m := by
      rw [allAns_evs_length (fun x hx => by
        obtain ⟨⟨i, hi⟩, rfl⟩ := List.mem_ofFn.1 hx; exact hωA i)]
      simp [streamTake]
    rw [List.take_left' hE]
  -- the chatter of `X` as a productive stream of the triple
  have hC : HLinked2.RoundInfC (profile o) X IeX IiX u π j vs ω := by
    refine ⟨f, xs, q, c, ds, πs, fun k => (flatSeg seg k).length, hck, hf1, hf2, hp0, hπ0, rfl,
      fun k => ⟨(hk k).1, (hk k).2.1, (hk k).2.2.1, ?_⟩, fun n => ?_⟩
    · show streamTake ω (flatSeg seg (k + 1)).length =
        streamTake ω (flatSeg seg k).length ++ seg k
      rw [← hflat, ← hflat]; rfl
    · obtain ⟨k, hk'⟩ := hu n; exact ⟨k, hk'.le⟩
  have hq : X.toL2.typedQ (j.val, .vals vs) = some (j, vs) := LinkedSessionEquiv.typedQ_typed hvs
  have hqY := LinkedSessionEquiv.typedQ_castL hty (j.val, .vals vs)
  rw [hq] at hqY
  simp only [Option.map_some] at hqY
  have hlegal : ∀ i, HLinked2.hostLegal X.host (ω i).1 (ω i).2 := by
    intro i
    obtain ⟨R', hR'⟩ := hvis (i + 1)
    rw [SessionLegal.streamTake_succ] at hR'
    obtain ⟨_, _, hR₂⟩ := visRun_split hR'
    exact visRun_legal hR₂ _ List.mem_cons_self
  let ωL : ℕ → Call (HLinked2.hostSig X.host) := fun i => ⟨(ω i).1, ⟨(ω i).2, hlegal i⟩⟩
  have hmem : ωL ∈ (HLinked2.compTripleS (profile o) X IeX IiX).2.2 (u, π, R) (j.val, .vals vs) := by
    show (fun i => StratLegal.liftCall (ωL i)) ∈
      HLinked2.compInf (profile o) X IeX IiX (u, π, R) (j.val, .vals vs)
    simp only [HLinked2.compInf, hq]
    exact ⟨hC, hvis⟩
  rw [(hB _ _ hRel).inf] at hmem
  change (fun i => StratLegal.liftCall (ωL i)) ∈
    HLinked2.compInf (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY (u', π', R) (j.val, .vals vs) at hmem
  rw [show (fun i => StratLegal.liftCall (ωL i)) = ω from rfl] at hmem
  simp only [HLinked2.compInf, hqY] at hmem
  obtain ⟨⟨f', xs', q', c', ds', πs', N, hck', hf1', hf2', hp0', hπ0', hN0, hk', hunb⟩, -⟩ := hmem
  -- read back as a `RoundInf` of `Y` under the same host
  choose stAt hstAt using hpre
  have hst0' : stAt 0 = st := hostRun_det (hstAt 0) (by simpa [streamTake] using HostRun.nil (g := G) st)
  refine ⟨IeY, IiY, hs', u', π', fun k => stAt (N k), hIe', hIi', hS', hr', ⟨f', xs', q', c', ds', πs',
    hck', hf1', hf2', hp0', hπ0', by simp [hN0, hst0'], fun k => ⟨(hk' k).1, (hk' k).2.1,
    (hk' k).2.2.1, ?_⟩⟩, fun N₀ => ?_⟩
  · have h := hstAt (N (k + 1))
    rw [(hk' k).2.2.2] at h
    obtain ⟨t, h₁, h₂⟩ := hostRun_append.1 h
    obtain rfl := hostRun_det h₁ (hstAt (N k))
    exact h₂
  · obtain ⟨k, hk''⟩ := hunb N₀
    refine ⟨N k, k, hk'', ?_⟩
    rw [(hostRun_of_logG (hstAt (N k))).2, hev]

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
