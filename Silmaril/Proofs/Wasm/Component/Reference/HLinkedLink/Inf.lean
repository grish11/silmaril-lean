module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.Fin

/-!
# The productive streams of the generic link (proofs)

`inf_eq`: the productive streams of the open triple (`HLinked2.compInfO`: host chatter
`RoundInfC`) are those of the generic link `HLinked2.linkO`. The server has no streams, so the
streams of the link are client streams served coherently with infinitely many host calls. The
round prefix of a client stream is absorbed into the chain of calls of `RoundInfC` (every call of
the prefix is a component call: a trapped call ends the round, `prefix_trap_false`), and the host
calls of the served rounds are the stream `ω`, in order.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.SessionLink (linkS served servedLog InfServe logTake linkEnd)
open Silmaril.Games.Abstract.StratThread (Rounds)
open Silmaril.Games.Abstract.SessionRoute (callS mapS)
open Silmaril.Games.Abstract.StratSession (pairS)
open Silmaril.Games.Abstract.SessionExt (routeS foldS)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance Answer)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession (WTH wth_of)
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
  (hostCalls_append hostCalls_one_wired hostCalls_one_host)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "IRel" => Silmaril.Wasm.Component.Reference.ImpRel

variable {P : Profile} {l : HLinked2} {Ie Ii : ScalarInstance}

/-! ## Bookkeeping -/

theorem serverO_inf (σ : PUnit.{1} × Store Nat) (a : Nat × Payload) :
    (l.serverO P Ie).2.2 σ a = ∅ := by
  show Sum.elim (l.hostPass.2.2 σ.1) ((l.expTripleH P Ie).2.2 σ.2) (l.route a) = ∅
  rcases l.route a with m | a' <;> rfl

theorem logTake_succ {E : Sig.{0}} (lg : ℕ → List (Call E)) (k : ℕ) :
    logTake lg (k + 1) = logTake lg k ++ lg k := by
  simp only [logTake, streamTake]
  rw [List.ofFn_succ_last]
  simp

theorem length_streamTake {α : Type} (ω : ℕ → α) (n : ℕ) : (streamTake ω n).length = n := by
  simp [streamTake]

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]
  | _, _, .nil, i, h, _ => absurd h (by simp)
  | _, _, .cons hr _, 0, _, _ => hr
  | _, _, .cons _ ht, i + 1, h₁, h₂ => by
    simpa using forall₂_getElem ht i (by simpa using h₁) (by simpa using h₂)

theorem streamAppend_map {α β : Type} (g : α → β) (L : List α) (y : ℕ → α) :
    Shape.streamAppend (L.map g) (fun k => g (y k)) = fun k => g (Shape.streamAppend L y k) := by
  funext k
  by_cases h : k < L.length
  · rw [Shape.streamAppend_lt (by simpa using h), Shape.streamAppend_lt h]
    simp
  · rw [Shape.streamAppend_ge (by simpa using Nat.le_of_not_lt h),
      Shape.streamAppend_ge (Nat.le_of_not_lt h)]
    simp

/-- **The states along a path of calls.** -/
theorem path_states {f : Ii.F.Op} :
    ∀ {L : List (Σ e : Ii.E.Op, Ii.E.Ar e)} {x y : Ii.HState},
      Ii.Path P x (callMoves L) y → ∃ st : ℕ → Ii.HState, st 0 = x ∧ st L.length = y ∧
        ∀ (i : ℕ) (hi : i < L.length), Ii.Path P (st i) (callMoves [L[i]]) (st (i + 1))
  | [], x, y, h => by
    cases h
    exact ⟨fun _ => x, rfl, rfl, fun i hi => absurd hi (by simp)⟩
  | c :: L, x, y, h => by
    rw [show c :: L = [c] ++ L from rfl, LinkedGLink.callMoves_append] at h
    obtain ⟨x₁, h₁, h₂⟩ := LinkedGLink.path_split h
    obtain ⟨st, h0, hL, hst⟩ := path_states (f := f) h₂
    refine ⟨fun i => match i with | 0 => x | i + 1 => st i, rfl, hL, ?_⟩
    intro i hi
    cases i with
    | zero => simpa [h0] using h₁
    | succ i => simpa using hst i (by simpa using hi)

/-- **A round prefix followed by one more call relates every call to one component call.** -/
theorem prefix_singletons {u : Store Nat} {f : Ii.F.Op} {x y : Ii.HState}
    {c : Σ e : Ii.E.Op, Ii.E.Ar e} :
    ∀ (pre : List (Σ e : Ii.E.Op, Ii.E.Ar e)) {cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)}
      {dss : List (List l.imp.ICall)},
      Ii.Path P (.idle u) (.inr (.ask f) :: callMoves (pre ++ cs)) x →
      Ii.Path P x (callMoves [c]) y → List.Forall₂ (IRel l.imp Ii) cs dss →
      ∃ zs : List l.imp.ICall, dss = zs.map (fun z => [z]) ∧
        List.Forall₂ (fun x z => IRel l.imp Ii x [z]) cs zs
  | _, [], [], _, _, .nil => ⟨[], rfl, .nil⟩
  | pre, x₀ :: cs, ds :: dss, hp, hc, .cons hx hrest => by
    rcases LinkedGLink.impRel_len hx with rfl | ⟨z, rfl⟩
    · rcases LinkedGLink.impRel_cases hx with ⟨-, htr⟩ | ⟨_, _, _, _, _, -, -, h, -⟩
      · rw [LinkedGLink.sigma_trap htr] at hp
        exact (LinkedGLink.prefix_trap_false hp hc).elim
      · cases h
    · obtain ⟨zs, rfl, hzs⟩ := prefix_singletons (pre ++ [x₀]) (by simpa using hp) hc hrest
      exact ⟨z :: zs, rfl, .cons hx hzs⟩

theorem flatten_map_singleton {α : Type} (L : List α) : (L.map fun z => [z]).flatten = L := by
  induction L with
  | nil => rfl
  | cons z L ih => simp [ih]

/-! ## The productive streams -/

/-- **The productive streams of the open triple are those of the generic link.** -/
theorem inf_eq (hw : l.WireTy) (u π : Store Nat) (q : Nat × Payload) :
    HLinked2.compInfO P l Ie Ii (u, π) q = (l.linkO P Ie Ii).2.2 ((PUnit.unit, π), u) q := by
  ext ω
  rcases hq : l.toL2.typedQ q with _ | ⟨j, vs⟩
  · -- an ill-typed question
    have hnt := typedQ_none hq
    simp only [HLinked2.compInfO, hq, Set.mem_empty_iff_false, false_iff]
    rintro (⟨rs, s₁, a, ω', -, -, hω', -⟩ | ⟨ω', hω', -⟩)
    · rw [serverO_inf] at hω'
      exact hω'
    · obtain ⟨j, vs, f, cs, dss, s, t, r, cc, y, rfl, hlow, -⟩ := hω'
      exact hnt (LinkedGLink.typedQ_of_lowered hlow)
  · obtain ⟨rfl, hck⟩ := LinkedSessionEquiv.typedQ_some hq
    simp only [HLinked2.compInfO, hq]
    constructor
    · -- host chatter is a served client stream
      rintro ⟨f, xs, qs, c, ds, πs, N, hcl, hf1, hf2, hq0, hπ0, hN0, hall, hunb⟩
      have h₀ : Ii.Path P (.idle u) (.inr (.ask f) :: callMoves ([] : List (Σ e : Ii.E.Op,
          Ii.E.Ar e))) (qs 0) := hq0
      have hr : ∀ k, Ii.Path P (qs k) (callMoves [c k]) (qs (k + 1)) := fun k => (hall k).1
      have hsing : ∀ k, ∃ y, ds k = [y] := by
        intro k
        rcases LinkedGLink.impRel_cases (hall k).2.1 with ⟨-, htr⟩ |
          ⟨_, _, _, _, _, -, -, h, -⟩
        · exact (LinkedGLink.chain_trap_false h₀ hr k htr).elim
        · exact ⟨_, h⟩
      choose y hy using hsing
      have hrel : ∀ k, IRel l.imp Ii (c k) [y k] := fun k => hy k ▸ (hall k).2.1
      have hrun : ∀ k, HLinked2.ExpRunH P l Ie (πs k) [y k] (πs (k + 1)) :=
        fun k => hy k ▸ (hall k).2.2.1
      obtain ⟨s, t, hs⟩ := LinkedGLink.path_idle_running h₀
      have hinf : InfServe (l.serverO P Ie) (PUnit.unit, π)
          (fun k => l.imp.wireCall l.wireH (y k)) (fun k => l.hostCalls [y k])
          (fun k => (PUnit.unit, πs k)) :=
        ⟨by rw [hπ0], fun k => round_of_expRunH_single (wth_of_impRel hw (hrel k)) (hrun k)⟩
      have hlog : ∀ k, logTake (fun k => l.hostCalls [y k]) k = streamTake ω (N k) := by
        intro k
        induction k with
        | zero => simp [logTake, streamTake, hN0]
        | succ k ih =>
          rw [logTake_succ, ih, (hall k).2.2.2, hy k]
      refine .inr ⟨_, ⟨j, vs, f, [], [], s, t, qs, c, y, rfl, ⟨xs, hcl, hf1, hf2, .nil⟩,
        by rw [← hs]; exact h₀, hs, fun k => ⟨hr k, hrel k⟩, ?_⟩, _, _, hinf, ?_, ?_⟩
      · simp [SimpleI.wireLog, Shape.streamAppend_nil]
      · intro n
        obtain ⟨k, hk⟩ := hunb n
        exact ⟨k, by rw [hlog, length_streamTake]; exact hk⟩
      · intro k
        rw [hlog, length_streamTake]
    · -- a served client stream is host chatter
      rintro (⟨rs, s₁, a, ω', -, -, hω', -⟩ | ⟨ω', hω', lg, st, hinf, hunb, hcoh⟩)
      · rw [serverO_inf] at hω'
        exact hω'.elim
      obtain ⟨j', vs', f, cs, dss, s, t, r, cc, y, hq', hlow, hp, hr0, hall, rfl⟩ := hω'
      simp only [Prod.mk.injEq, Payload.vals.injEq] at hq'
      obtain ⟨hj, rfl⟩ := hq'
      obtain rfl : j' = j := Fin.ext hj.symm
      obtain ⟨xs, hcl, hf1, hf2, hF⟩ := hlow
      have hr : ∀ k, Ii.Path P (r k) (callMoves [cc k]) (r (k + 1)) := fun k => (hall k).1
      have hp' : Ii.Path P (.idle u) (.inr (.ask f) :: callMoves ([] ++ cs)) (r 0) := by
        rw [hr0]; exact hp
      obtain ⟨zs, rfl, hzs⟩ := prefix_singletons [] hp' (hr 0) hF
      have hlen : zs.length = cs.length := hzs.length_eq.symm
      -- the calls of the round, prefix and chain
      set Cc : ℕ → Σ e : Ii.E.Op, Ii.E.Ar e := Shape.streamAppend cs cc with hCc
      set Y : ℕ → l.imp.ICall := Shape.streamAppend zs y with hY
      have hrelY : ∀ k, IRel l.imp Ii (Cc k) [Y k] := by
        intro k
        by_cases hk : k < cs.length
        · rw [hCc, hY, Shape.streamAppend_lt hk, Shape.streamAppend_lt (by omega)]
          exact forall₂_getElem hzs k hk (by omega)
        · rw [hCc, hY, Shape.streamAppend_ge (Nat.le_of_not_lt hk),
            Shape.streamAppend_ge (by omega), hlen]
          exact (hall _).2
      have hω' : Shape.streamAppend (l.imp.wireLog l.wireH (zs.map fun z => [z]).flatten)
          (fun k => l.imp.wireCall l.wireH (y k)) = fun k => l.imp.wireCall l.wireH (Y k) := by
        rw [flatten_map_singleton, SimpleI.wireLog, streamAppend_map]
      rw [hω'] at hinf
      -- the states of the round
      obtain ⟨x₀, hx₀, hx₁⟩ := LinkedGLink.path_split (l₁ := [.inr (.ask f)]) hp
      obtain ⟨pst, hp0, hpL, hpst⟩ := path_states (f := f) hx₁
      set Q : ℕ → Ii.HState := fun k => if k < cs.length then pst k else r (k - cs.length)
        with hQ
      have hQ0 : Q 0 = x₀ := by
        by_cases h0 : 0 < cs.length
        · simp [hQ, h0, hp0]
        · have hcs : cs.length = 0 := by omega
          show (if 0 < cs.length then pst 0 else r (0 - cs.length)) = _
          simp only [h0, ite_false]; rw [Nat.zero_sub, hr0, ← hpL, hcs, hp0]
      have hQstep : ∀ k, Ii.Path P (Q k) (callMoves [Cc k]) (Q (k + 1)) := by
        intro k
        by_cases hk : k < cs.length
        · have h1 := hpst k hk
          have hQk : Q k = pst k := by simp [hQ, hk]
          have hQk1 : Q (k + 1) = pst (k + 1) := by
            by_cases hk1 : k + 1 < cs.length
            · simp [hQ, hk1]
            · have he : k + 1 = cs.length := by omega
              show (if k + 1 < cs.length then pst (k + 1) else r (k + 1 - cs.length)) = _
              simp only [hk1, ite_false]; rw [he, Nat.sub_self, hr0, hpL]
          rw [hQk, hQk1, hCc, Shape.streamAppend_lt hk]
          exact h1
        · have hQk : Q k = r (k - cs.length) := by simp [hQ, hk]
          have hQk1 : Q (k + 1) = r (k - cs.length + 1) := by
            have hk1 : ¬ k + 1 < cs.length := by omega
            show (if k + 1 < cs.length then pst (k + 1) else r (k + 1 - cs.length)) = _
            simp only [hk1, ite_false]
            congr 1
            omega
          rw [hQk, hQk1, hCc, Shape.streamAppend_ge (Nat.le_of_not_lt hk)]
          exact hr _
      have hstep : ∀ k, HLinked2.ExpRunH P l Ie (st k).2 [Y k] (st (k + 1)).2 ∧
          lg k = l.hostCalls [Y k] :=
        fun k => expRunH_single_of_round (wth_of_impRel hw (hrelY k)) (hinf.step k)
      refine ⟨f, xs, Q, Cc, fun k => [Y k], fun k => (st k).2, fun k => (logTake lg k).length,
        hcl, hf1, hf2, by rw [hQ0]; exact hx₀, by show (st 0).2 = π; rw [hinf.zero], rfl,
        fun k => ⟨hQstep k,
          hrelY k, (hstep k).1, ?_⟩, hunb⟩
      rw [hcoh, hcoh, logTake_succ, (hstep k).2]

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink
