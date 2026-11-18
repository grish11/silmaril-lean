module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Trap
import Silmaril.Proofs.Wasm.Component.Reference.FloatSound

/-!
# Host runs and sessions under one host

* `hostAnswersS_det`, `hostRun_det`, `hostRun_append`, `hostRun_compat`: a deterministic host
  answers the same call in the same state alike; host runs split along lists;
* `hostRun_logG`, `hostRun_of_logG`: the logging host is the host with its log of answered
  calls (`evs`);
* `hostRun_scriptG_state`, `hostRun_scriptG_prefix`: the scripted host counts answered calls and
  realizes every prefix of a realizable history;
* `round_same`: two rounds from the same stores ask the same host calls until their answers
  first differ (`HostSame`);
* `sess_unique`: at `profile o`, two sessions of the same calls under the same host from the same
  host state are equal.
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
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionObs (mem_ask_of fOp_ext)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Host runs -/

section HostRuns

variable {τ : Type} {g : τ → HostFuncId → List RVal → Option (List RVal × τ)} {n : Nat}

theorem hostAnswersS_det {s s₁ s₂ : τ} {d d' : Call (sigN n)} (h : HostAnswersS g s d s₁)
    (h' : HostAnswersS g s d' s₂) (he : d.1 = d'.1) : d.2 = d'.2 ∧ s₁ = s₂ := by
  obtain ⟨m, R⟩ := d
  obtain ⟨m', R'⟩ := d'
  simp only at he
  subst he
  obtain ⟨k, ws, hm, hA⟩ := h
  obtain ⟨k', ws', hm', hA'⟩ := h'
  simp only at hm hm' hA hA'
  rw [hm] at hm'
  simp only [Prod.mk.injEq, Payload.vals.injEq] at hm'
  obtain ⟨rfl, rfl⟩ := hm'
  rcases R with _ | ⟨fs | us⟩ <;> rcases R' with _ | ⟨fs' | us'⟩ <;> simp only at hA hA'
  · exact ⟨rfl, hA.2.trans hA'.2.symm⟩
  · rw [hA.1] at hA'; cases hA'
  · rw [hA'.1] at hA; cases hA
  · rw [hA] at hA'
    simp only [Option.some.injEq, Prod.mk.injEq] at hA'
    obtain ⟨hu, rfl⟩ := hA'
    rw [map_toRefVal_inj hu]
    exact ⟨rfl, rfl⟩

theorem hostRun_det {s s₁ s₂ : τ} {H : List (Call (sigN n))} (h : HostRun g s H s₁)
    (h' : HostRun g s H s₂) : s₁ = s₂ := by
  induction h generalizing s₂ with
  | nil => cases h'; rfl
  | cons hd _ ih =>
    cases h' with
    | cons hd' hr' =>
      obtain ⟨-, rfl⟩ := hostAnswersS_det hd hd' rfl
      exact ih hr'

theorem hostRun_append {s s₂ : τ} :
    ∀ {H₁ H₂ : List (Call (sigN n))},
      HostRun g s (H₁ ++ H₂) s₂ ↔ ∃ s₁, HostRun g s H₁ s₁ ∧ HostRun g s₁ H₂ s₂
  | [], _ => ⟨fun h => ⟨s, .nil s, h⟩, fun ⟨_, h₁, h₂⟩ => by cases h₁; exact h₂⟩
  | d :: H₁, H₂ => by
    constructor
    · intro h
      cases h with
      | cons hd hr =>
        obtain ⟨s₁, h₁, h₂⟩ := (hostRun_append (H₁ := H₁) (H₂ := H₂)).1 hr
        exact ⟨s₁, .cons hd h₁, h₂⟩
    · rintro ⟨s₁, h₁, h₂⟩
      cases h₁ with
      | cons hd hr => exact .cons hd ((hostRun_append (H₁ := H₁) (H₂ := H₂)).2 ⟨s₁, hr, h₂⟩)

theorem hostRun_compat {s s₁ s₂ : τ} {H₁ H₂ : List (Call (sigN n))} (h : HostRun g s H₁ s₁)
    (h' : HostRun g s H₂ s₂) : HostCompat H₁ H₂ := by
  induction h generalizing H₂ s₂ with
  | nil => cases H₂ <;> trivial
  | cons hd _ ih =>
    cases h' with
    | nil => trivial
    | cons hd' hr' =>
      intro he
      obtain ⟨h2, rfl⟩ := hostAnswersS_det hd hd' he
      exact ⟨h2, ih hr'⟩

end HostRuns

/-! ## The log -/

/-- The log entries of the answered calls of a history. -/
def evs {n : Nat} (H : List (Call (sigN n))) : List HLinked2.HostEvent :=
  (HLinked2.answered H).map fun e => (⟨e.1.val⟩, e.2.1.map toRefVal, e.2.2.map toRefVal)

theorem answered_cons_none {n : Nat} (m : (sigN n).Op) (H : List (Call (sigN n))) :
    HLinked2.answered (⟨m, none⟩ :: H) = HLinked2.answered H := by
  obtain ⟨k, _ | _⟩ := m <;> rfl

theorem answered_cons_vals {n : Nat} (k : Fin n) (ws us : List IVal) (H : List (Call (sigN n))) :
    HLinked2.answered (⟨(k, .vals ws), some (.vals us)⟩ :: H) =
      (k, ws, us) :: HLinked2.answered H := rfl

theorem answered_append {n : Nat} :
    ∀ H K : List (Call (sigN n)),
      HLinked2.answered (H ++ K) = HLinked2.answered H ++ HLinked2.answered K
  | [], _ => rfl
  | ⟨(k, p), R⟩ :: H, K => by
    rcases p with fs | ws <;> rcases R with _ | ⟨fs' | us⟩ <;>
      simp [HLinked2.answered, answered_append H K]

theorem evs_append {n : Nat} (H K : List (Call (sigN n))) : evs (H ++ K) = evs H ++ evs K := by
  simp [evs, answered_append]

theorem answered_of_evs {n : Nat} {H K : List (Call (sigN n))} (h : evs H = evs K) :
    HLinked2.answered H = HLinked2.answered K := by
  refine List.map_injective_iff.2 ?_ h
  rintro ⟨k, ws, us⟩ ⟨k', ws', us'⟩ he
  simp only [Prod.mk.injEq, HostFuncId.mk.injEq] at he
  obtain ⟨hk, hw, hu⟩ := he
  rw [Fin.ext hk, map_toRefVal_inj hw, map_toRefVal_inj hu]

section Log

variable {σ : Type} {g : σ → HostFuncId → List RVal → Option (List RVal × σ)} {n : Nat}

theorem hostRun_logG {s s' : σ} {H : List (Call (sigN n))} (h : HostRun g s H s') :
    ∀ L, HostRun (HLinked2.logG g) (s, L) H (s', L ++ evs H) := by
  induction h with
  | nil s => intro L; simpa [evs, HLinked2.answered] using HostRun.nil (g := HLinked2.logG g) (s, L)
  | @cons s s₁ s₂ d ds hd _ ih =>
    intro L
    obtain ⟨m, R⟩ := d
    obtain ⟨k, ws, hm, hA⟩ := hd
    simp only at hm hA
    subst hm
    rcases R with _ | ⟨fs | us⟩
    · obtain ⟨hg, rfl⟩ := hA
      refine .cons ⟨k, ws, rfl, ?_, rfl⟩ ?_
      · simp [HLinked2.logG, hg]
      · have e : evs (⟨(k, .vals ws), none⟩ :: ds) = evs ds := rfl
        rw [e]
        exact ih L
    · exact hA.elim
    · refine .cons (s₁ := (s₁, L ++ [(⟨k.val⟩, ws.map toRefVal, us.map toRefVal)]))
        ⟨k, ws, rfl, ?_⟩ ?_
      · simp [HLinked2.logG, hA]
      · have e : evs (⟨(k, .vals ws), some (.vals us)⟩ :: ds) =
            [(⟨k.val⟩, ws.map toRefVal, us.map toRefVal)] ++ evs ds := rfl
        rw [e, ← List.append_assoc]
        exact ih _

theorem hostRun_of_logG {p p' : σ × List HLinked2.HostEvent} {H : List (Call (sigN n))}
    (h : HostRun (HLinked2.logG g) p H p') : HostRun g p.1 H p'.1 ∧ p'.2 = p.2 ++ evs H := by
  induction h with
  | nil p => exact ⟨.nil _, by simp [evs, HLinked2.answered]⟩
  | @cons p p₁ p₂ d ds hd _ ih =>
    obtain ⟨m, R⟩ := d
    obtain ⟨k, ws, hm, hA⟩ := hd
    simp only at hm hA
    subst hm
    rcases R with _ | ⟨fs | us⟩
    · obtain ⟨hg, rfl⟩ := hA
      simp only [HLinked2.logG, Option.map_eq_none_iff] at hg
      have e : evs (⟨(k, .vals ws), none⟩ :: ds) = evs ds := rfl
      exact ⟨.cons ⟨k, ws, rfl, hg, rfl⟩ ih.1, by rw [e]; exact ih.2⟩
    · exact hA.elim
    · simp only [HLinked2.logG, Option.map_eq_some_iff] at hA
      obtain ⟨⟨rs, t⟩, hg, he⟩ := hA
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨.cons ⟨k, ws, rfl, hg⟩ ih.1, ?_⟩
      have e : evs (⟨(k, .vals ws), some (.vals us)⟩ :: ds) =
          [(⟨k.val⟩, ws.map toRefVal, us.map toRefVal)] ++ evs ds := rfl
      rw [ih.2, e, ← List.append_assoc]

end Log

/-! ## The scripted host -/

theorem hostRun_scriptG_state {n : Nat} {S : List (Fin n × List IVal × List IVal)} {i j : ℕ}
    {H : List (Call (sigN n))} (h : HostRun (HLinked2.scriptG S) i H j) :
    j = i + (HLinked2.answered H).length := by
  induction h with
  | nil => simp [HLinked2.answered]
  | @cons s s₁ s₂ d ds hd _ ih =>
    obtain ⟨m, R⟩ := d
    obtain ⟨k, ws, hm, hA⟩ := hd
    simp only at hm hA
    subst hm
    rcases R with _ | ⟨fs | us⟩
    · obtain ⟨-, rfl⟩ := hA
      rw [ih, answered_cons_none]
    · exact hA.elim
    · simp only [HLinked2.scriptG] at hA
      split at hA
      · split_ifs at hA
        simp only [Option.some.injEq, Prod.mk.injEq] at hA
        obtain ⟨-, rfl⟩ := hA
        rw [ih, answered_cons_vals]
        simp only [List.length_cons]
        omega
      · cases hA

/-- **The scripted host of a realizable history realizes each of its prefixes.** -/
theorem hostRun_scriptG_prefix {l : HLinked2} {R' : List (sigN l.host.length).Op}
    {H K : List (Call (sigN l.host.length))} (hr : HLinked2.RealRun l.host [] (H ++ K) R')
    (hv : HLinked2.ValsCalls (H ++ K)) :
    l.HostTyped (HLinked2.scriptG (HLinked2.answered (H ++ K))) ∧
      HostRun (HLinked2.scriptG (HLinked2.answered (H ++ K))) 0 H (HLinked2.answered H).length := by
  obtain ⟨hT, hR⟩ := hostRun_scriptG hr hv
  obtain ⟨s₁, h₁, -⟩ := hostRun_append.1 hR
  refine ⟨hT, ?_⟩
  have := hostRun_scriptG_state h₁
  rw [this, Nat.zero_add] at h₁
  exact h₁

/-! ## Rounds asking the same host calls -/

/-- **The same host calls until the answers first differ**: the same next call while the answers
agree, and the same length when they agree throughout. -/
def HostSame {n : Nat} : List (Call (sigN n)) → List (Call (sigN n)) → Prop
  | x :: xs, y :: ys => x.1 = y.1 ∧ (x.2 = y.2 → HostSame xs ys)
  | [], [] => True
  | _, _ => False

variable {l : HLinked2} {Ie Ii : SInst} {o : GrowOracle}

theorem impRel_same {c c' : Σ e : Ii.E.Op, Ii.E.Ar e}
    {ds ds' : List (Call (sigN l.imp.imports.length))} {π πa πb : Store Nat}
    (he : c.1 = c'.1) (h : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c ds)
    (h' : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c' ds')
    (r : HLinked2.ExpRunH (profile o) l Ie π ds πa)
    (r' : HLinked2.ExpRunH (profile o) l Ie π ds' πb) :
    (l.hostCalls ds = [] ∧ l.hostCalls ds' = [] ∧ c = c' ∧ ds = ds' ∧ πa = πb) ∨
      (∃ x y, l.hostCalls ds = [x] ∧ l.hostCalls ds' = [y] ∧ x.1 = y.1 ∧
        (x.2 = y.2 → c = c' ∧ ds = ds' ∧ πa = πb)) := by
  have key : (l.hostCalls ds = [] ∧ l.hostCalls ds' = []) ∨
      (∃ x y, l.hostCalls ds = [x] ∧ l.hostCalls ds' = [y] ∧ x.1 = y.1) := by
    obtain ⟨e, n⟩ := c
    obtain ⟨e', n'⟩ := c'
    simp only at he
    subst he
    obtain ⟨nm, ft, A, hi, hA, hm⟩ := h
    obtain ⟨nm', ft', A', hi', hA', hm'⟩ := h'
    rw [hi] at hi'
    cases hi'
    simp only at hm hm'
    cases hl : liftArgs ft.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
    | none =>
      rw [hl] at hm hm'
      obtain ⟨-, rfl⟩ := hm
      obtain ⟨-, rfl⟩ := hm'
      exact .inl ⟨rfl, rfl⟩
    | some ws =>
      rw [hl] at hm hm'
      obtain ⟨hk, R, rfl, -⟩ := hm
      obtain ⟨hk', R', rfl, -⟩ := hm'
      cases r with
      | ret w hw _ _ => exact .inl ⟨hostCalls_one_wired hw, hostCalls_one_wired hw⟩
      | trap w hw _ _ => exact .inl ⟨hostCalls_one_wired hw, hostCalls_one_wired hw⟩
      | host i hi _ =>
        exact .inr ⟨_, _, hostCalls_one_host i hi, hostCalls_one_host i hi, rfl⟩
  rcases key with ⟨h1, h2⟩ | ⟨x, y, h1, h2, hxy⟩
  · obtain ⟨hc, hd, hπ, -⟩ := impRelH_det (X := []) (Y := []) he h h' r r'
      (by rw [h1, h2]; trivial)
    exact .inl ⟨h1, h2, hc, hd, hπ⟩
  · refine .inr ⟨x, y, h1, h2, hxy, fun h2' => ?_⟩
    obtain ⟨hc, hd, hπ, -⟩ := impRelH_det (X := []) (Y := []) he h h' r r'
      (by rw [h1, h2]; exact fun _ => ⟨h2', trivial⟩)
    exact ⟨hc, hd, hπ⟩

theorem callsH_same {u : Store Nat} {f : Ii.F.Op} :
    ∀ (cs cs' : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss dss' : List (List (Call (sigN l.imp.imports.length))))
      (pre : List (Move Ii.E Ii.F)) (w w' : Ii.F.Ar f) (π π₁ π₂ : Store Nat),
      pre ++ (Silmaril.Wasm.Component.Reference.callMoves cs ++ [.inr (.ans f w)]) ∈
        Ii.strategy (profile o) u →
      pre ++ (Silmaril.Wasm.Component.Reference.callMoves cs' ++ [.inr (.ans f w')]) ∈
        Ii.strategy (profile o) u →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs' dss' →
      HLinked2.ExpRunH (profile o) l Ie π dss.flatten π₁ →
      HLinked2.ExpRunH (profile o) l Ie π dss'.flatten π₂ →
      HostSame (l.hostCalls dss.flatten) (l.hostCalls dss'.flatten)
  | [], [], _, _, _, _, _, _, _, _, _, _, hr, hr', _, _ => by
    cases hr
    cases hr'
    trivial
  | [], c' :: cs', _, _, pre, w, w', π, π₁, π₂, h, h', _, _, _, _ => by
    exfalso
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic h (mem_ask_of h') trivial
    cases e
  | c :: cs, [], _, _, pre, w, w', π, π₁, π₂, h, h', _, _, _, _ => by
    exfalso
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic (mem_ask_of h) h' trivial
    cases e
  | c :: cs, c' :: cs', dss, dss', pre, w, w', π, π₁, π₂, h, h', hr, hr', r, r' => by
    obtain ⟨ds, dss₁, hd, hr₁, rfl⟩ := List.forall₂_cons_left_iff.mp hr
    obtain ⟨ds', dss₁', hd', hr₁', rfl⟩ := List.forall₂_cons_left_iff.mp hr'
    rw [List.flatten_cons] at r r'
    simp only [List.flatten_cons, hostCalls_append]
    obtain ⟨πa, ra, rb⟩ := HLinkedSession.expRunH_split _ _ r
    obtain ⟨πb, ra', rb'⟩ := HLinkedSession.expRunH_split _ _ r'
    have hm : ∀ (x : Σ e : Ii.E.Op, Ii.E.Ar e) (xs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
        (v : Ii.F.Ar f),
        pre ++ (Silmaril.Wasm.Component.Reference.callMoves (x :: xs) ++ [.inr (.ans f v)]) =
          (pre ++ [.inl (.ask x.1), .inl (.ans x.1 x.2)]) ++
            (Silmaril.Wasm.Component.Reference.callMoves xs ++ [.inr (.ans f v)]) := by
      intro x xs v
      obtain ⟨e, n⟩ := x
      simp [Silmaril.Wasm.Component.Reference.callMoves]
    have e := Silmaril.Wasm.Game.ScalarInstance.strategy_deterministic (mem_ask_of h)
      (mem_ask_of h') trivial
    simp only [Sum.inl.injEq, Ev.ask.injEq] at e
    rcases impRel_same e hd hd' ra ra' with ⟨h1, h2, rfl, rfl, rfl⟩ |
        ⟨x, y, h1, h2, hxy, himp⟩
    · simp only [h1, List.nil_append]
      rw [hm] at h h'
      exact callsH_same cs cs' dss₁ dss₁' _ w w' πa π₁ π₂ h h' hr₁ hr₁' rb rb'
    · simp only [h1, h2, List.singleton_append]
      refine ⟨hxy, fun hx => ?_⟩
      obtain ⟨rfl, rfl, rfl⟩ := himp hx
      rw [hm] at h h'
      exact callsH_same cs cs' dss₁ dss₁' _ w w' πa π₁ π₂ h h' hr₁ hr₁' rb rb'

/-- **Two rounds from the same stores ask the same host calls until their answers differ.** -/
theorem round_same {u π u₁ π₁ u₂ π₂ : Store Nat} {j : Fin l.imp.exports.length} {vs : List IVal}
    {o₁ o₂ : Option (List IVal)} {H₁ H₂ : List (Call (sigN l.host.length))}
    (h₁ : HLinked2.SessSpec (profile o) l Ie Ii u π [(j, vs)] [o₁] [H₁] u₁ π₁)
    (h₂ : HLinked2.SessSpec (profile o) l Ie Ii u π [(j, vs)] [o₂] [H₂] u₂ π₂) :
    HostSame H₁ H₂ := by
  obtain ⟨⟨j₁, vs₁, f, cs, w, dss⟩, rfl, rfl, ⟨xs, hck, hf₁, hf₂, hrel⟩, hp, he, -, rfl⟩ :=
    sessSpec_singleH h₁
  obtain ⟨⟨j₂, vs₂, f', cs', w', dss'⟩, hj, hv, ⟨xs', hck', hf₁', hf₂', hrel'⟩, hp', he', -,
    rfl⟩ := sessSpec_singleH h₂
  simp only at hj hv hck hf₁ hf₂ hrel hp he hck' hf₁' hf₂' hrel' hp' he' ⊢
  subst hj hv
  rw [hck] at hck'
  cases hck'
  obtain rfl : f = f' := fOp_ext (hf₁.trans hf₁'.symm) (hf₂.trans hf₂'.symm)
  have hm : ∀ (c : List (Σ e : Ii.E.Op, Ii.E.Ar e)) (v : Ii.F.Ar f),
      (.inr (.ask f) :: Silmaril.Wasm.Component.Reference.callMoves c ++ [.inr (.ans f v)] :
        List (Move Ii.E Ii.F)) =
        [.inr (.ask f)] ++ (Silmaril.Wasm.Component.Reference.callMoves c ++ [.inr (.ans f v)]) :=
    fun _ _ => rfl
  have hs := (Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff).mpr ⟨_, hp⟩
  have hs' := (Silmaril.Wasm.Game.ScalarInstance.mem_strategy_iff).mpr ⟨_, hp'⟩
  simp only [Linked2.SessRound.instMoves] at hs hs'
  rw [hm] at hs hs'
  exact callsH_same cs cs' dss dss' _ w w' π π₁ π₂ hs hs' hrel hrel' he he'

/-! ## Sessions under one host -/

theorem sessSpecH_nil_inv {P : Profile} {u π u' π' : Store Nat}
    {outs : List (Option (List IVal))} {hs : List (List (Call (sigN l.host.length)))}
    (h : HLinked2.SessSpec P l Ie Ii u π [] outs hs u' π') :
    outs = [] ∧ hs = [] ∧ u' = u ∧ π' = π := by
  cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem sessSpecH_cons_inv {P : Profile} {u π u' π' : Store Nat}
    {q : Fin l.imp.exports.length × List IVal} {cs : List (Fin l.imp.exports.length × List IVal)}
    {outs : List (Option (List IVal))} {hs : List (List (Call (sigN l.host.length)))}
    (h : HLinked2.SessSpec P l Ie Ii u π (q :: cs) outs hs u' π') :
    ∃ o os H hs₁ u₁ π₁, outs = o :: os ∧ hs = H :: hs₁ ∧
      HLinked2.SessSpec P l Ie Ii u π [q] [o] [H] u₁ π₁ ∧
      HLinked2.SessSpec P l Ie Ii u₁ π₁ cs os hs₁ u' π' := by
  generalize hq : q :: cs = calls at h
  cases h with
  | nil => cases hq
  | round d hok hp he hans hr =>
    simp only [List.cons.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    exact ⟨_, _, _, _, _, _, rfl, rfl, .round d hok hp he hans (.nil _ _), hr⟩

theorem sessSpecH_cons {P : Profile} {u π u₁ π₁ u' π' : Store Nat}
    {q : Fin l.imp.exports.length × List IVal} {cs : List (Fin l.imp.exports.length × List IVal)}
    {o : Option (List IVal)} {os : List (Option (List IVal))}
    {H : List (Call (sigN l.host.length))} {hs : List (List (Call (sigN l.host.length)))}
    (h₁ : HLinked2.SessSpec P l Ie Ii u π [q] [o] [H] u₁ π₁)
    (h₂ : HLinked2.SessSpec P l Ie Ii u₁ π₁ cs os hs u' π') :
    HLinked2.SessSpec P l Ie Ii u π (q :: cs) (o :: os) (H :: hs) u' π' := by
  generalize hq : [q] = calls at h₁
  cases h₁ with
  | round d hok hp he hans hr =>
    injection hq with hq1 hq2
    subst hq1 hq2
    obtain ⟨-, -, rfl, rfl⟩ := sessSpecH_nil_inv hr
    exact .round d hok hp he hans h₂

/-- **Sessions under one host are unique** (deterministic profiles). -/
theorem sess_unique {τ : Type} (g : τ → HostFuncId → List RVal → Option (List RVal × τ)) :
    ∀ (calls : List (Fin l.imp.exports.length × List IVal)) {u π u₁ π₁ u₂ π₂ : Store Nat}
      {outs outs' : List (Option (List IVal))} {hs hs' : List (List (Call (sigN l.host.length)))}
      {st st₁ st₂ : τ},
      HLinked2.SessSpec (profile o) l Ie Ii u π calls outs hs u₁ π₁ →
      HostRun g st hs.flatten st₁ →
      HLinked2.SessSpec (profile o) l Ie Ii u π calls outs' hs' u₂ π₂ →
      HostRun g st hs'.flatten st₂ →
      outs = outs' ∧ hs = hs' ∧ u₁ = u₂ ∧ π₁ = π₂ ∧ st₁ = st₂
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, h, hr, h', hr' => by
    obtain ⟨rfl, rfl, rfl, rfl⟩ := sessSpecH_nil_inv h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := sessSpecH_nil_inv h'
    cases hr; cases hr'
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | q :: cs, _, _, _, _, _, _, _, _, _, _, _, _, _, h, hr, h', hr' => by
    obtain ⟨o₁, os, H, hs₁, ua, πa, rfl, rfl, ha, hb⟩ := sessSpecH_cons_inv h
    obtain ⟨o₂, os', H', hs₁', ub, πb, rfl, rfl, ha', hb'⟩ := sessSpecH_cons_inv h'
    rw [List.flatten_cons] at hr hr'
    obtain ⟨sa, hra, hrb⟩ := hostRun_append.1 hr
    obtain ⟨sb, hra', hrb'⟩ := hostRun_append.1 hr'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := round_detH ha ha' (hostRun_compat hra hra')
    obtain rfl := hostRun_det hra hra'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := sess_unique g cs hb hrb hb' hrb'
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
