module

public import Silmaril.Wasm.Component.Reference.HLinkedSessionObj.Defs
public import Silmaril.Wasm.Component.Reference.HLinkedSession.Thms
import Silmaril.Proofs.Wasm.Component.Reference.FloatSound
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Sess

/-!
# Host-realizable histories

* `realRun_of_hostRun`: the host calls answered by a typed deterministic stateful host form a
  `RealRun` from no refusals: a refusal keeps the host state, so a call refused since the last
  answered call is refused again, and an import without typed results is never answered.
* `hostRun_scriptG`: conversely, a `RealRun` from no refusals on IR arguments is answered by the
  scripted host of its answered calls, which is typed.
* `not_hostRun_refuse_answer`: no host refuses a call and then answers it with nothing answered
  in between.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Runtime (HostFuncId)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val

variable {l : HLinked2} {τ : Type}

/-! ## From hosts to histories -/

/-- The calls of `R` are refused by `g` at the state `s`. -/
def Refuses (g : τ → HostFuncId → List RVal → Option (List RVal × τ)) {n : Nat}
    (R : List (sigN n).Op) (s : τ) : Prop :=
  ∀ m ∈ R, ∃ (k : Fin n) (ws : List IVal), m = (k, .vals ws) ∧ g s ⟨k.val⟩ (ws.map toRefVal) = none

theorem realRun_of_hostRun_aux (g : τ → HostFuncId → List RVal → Option (List RVal × τ))
    (hT : l.HostTyped g) {s s' : τ} {c : List (Call (sigN l.host.length))}
    (h : HostRun g s c s') :
    ∀ R, Refuses g R s → ∃ R', HLinked2.RealRun l.host R c R' ∧ Refuses g R' s' := by
  induction h with
  | nil s => exact fun R hR => ⟨R, .nil R, hR⟩
  | @cons s s₁ s₂ d ds hd _ ih =>
    intro R hR
    obtain ⟨m, R0⟩ := d
    obtain ⟨k, ws, hm, hA⟩ := hd
    simp only at hm hA
    subst hm
    rcases R0 with _ | ⟨fs | us⟩
    · obtain ⟨hg, rfl⟩ := hA
      by_cases hF : HLinked2.Forced l.host R (k, .vals ws)
      · obtain ⟨R', h₁, h₂⟩ := ih R hR
        exact ⟨R', .forced hF h₁, h₂⟩
      · have hR' : Refuses g ((k, Payload.vals ws) :: R) s₁ := by
          intro m hm'
          rcases List.mem_cons.1 hm' with rfl | hm'
          · exact ⟨k, ws, rfl, hg⟩
          · exact hR m hm'
        obtain ⟨R', h₁, h₂⟩ := ih _ hR'
        exact ⟨R', .refuse hF h₁, h₂⟩
    · exact hA.elim
    · have hnot : (k, Payload.vals ws) ∉ R := by
        intro hin
        obtain ⟨k', ws', he, hg'⟩ := hR _ hin
        simp only [Prod.mk.injEq, Payload.vals.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [hA] at hg'
        cases hg'
      obtain ⟨us', he, hck⟩ := hT s k.val k.isLt ws _ s₁ hA
      have hus : us = us' := map_toRefVal_inj he
      subst hus
      obtain ⟨R', h₁, h₂⟩ := ih [] (fun _ h => (List.not_mem_nil h).elim)
      refine ⟨R', .answer hnot ?_ h₁, h₂⟩
      simpa [HLinked2.hostLegal] using hck

/-- **The host calls answered by a typed host are a realizable history.** -/
theorem realRun_of_hostRun (g : τ → HostFuncId → List RVal → Option (List RVal × τ))
    (hT : l.HostTyped g) {s s' : τ} {c : List (Call (sigN l.host.length))}
    (h : HostRun g s c s') : ∃ R', HLinked2.RealRun l.host [] c R' :=
  let ⟨R', h₁, _⟩ := realRun_of_hostRun_aux g hT h [] (fun _ h => (List.not_mem_nil h).elim)
  ⟨R', h₁⟩

/-- The host calls answered by a host are on IR arguments. -/
theorem valsCalls_of_hostRun {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ))
    {n : Nat} {s s' : σ} {c : List (Call (sigN n))} (h : HostRun g s c s') :
    HLinked2.ValsCalls c := by
  induction h with
  | nil => exact fun _ h => (List.not_mem_nil h).elim
  | cons hd _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨k, ws, he, -⟩ := hd
      exact ⟨k, ws, he⟩
    · exact ih x hx

/-! ## The scripted host -/

/-- The first answered call of a realizable history is not among the refusals, and is legal. -/
theorem head_answered {h : Iface} {R R' : List (sigN h.length).Op}
    {c : List (Call (sigN h.length))} (hr : HLinked2.RealRun h R c R')
    (hv : HLinked2.ValsCalls c) {k : Fin h.length} {ws us : List IVal}
    (he : (HLinked2.answered c).head? = some (k, ws, us)) :
    (k, Payload.vals ws) ∉ R ∧ ValTy.checkList h[k].2.results us = true := by
  induction hr with
  | nil => simp [HLinked2.answered] at he
  | @forced R R' m c hF _ ih =>
    obtain ⟨k', ws', hm⟩ := hv _ List.mem_cons_self
    subst hm
    exact ih (fun x hx => hv x (List.mem_cons_of_mem _ hx)) (by simpa [HLinked2.answered] using he)
  | @refuse R R' m c hF _ ih =>
    obtain ⟨k', ws', hm⟩ := hv _ List.mem_cons_self
    subst hm
    obtain ⟨h₁, h₂⟩ :=
      ih (fun x hx => hv x (List.mem_cons_of_mem _ hx)) (by simpa [HLinked2.answered] using he)
    exact ⟨fun hin => h₁ (List.mem_cons_of_mem _ hin), h₂⟩
  | @answer R R' m p c hm hl _ _ =>
    obtain ⟨k', ws', hm'⟩ := hv _ List.mem_cons_self
    subst hm'
    rcases p with fs | us'
    · exact absurd hl (by simp [HLinked2.hostLegal])
    · simp only [HLinked2.answered, List.head?_cons, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact ⟨hm, hl⟩

/-- The answered calls of a realizable history are legal. -/
theorem answered_legal {h : Iface} {R R' : List (sigN h.length).Op}
    {c : List (Call (sigN h.length))} (hr : HLinked2.RealRun h R c R')
    (hv : HLinked2.ValsCalls c) :
    ∀ e ∈ HLinked2.answered c, ValTy.checkList h[e.1].2.results e.2.2 = true := by
  induction hr with
  | nil => simp [HLinked2.answered]
  | @forced R R' m c _ _ ih =>
    obtain ⟨k', ws', hm⟩ := hv _ List.mem_cons_self
    subst hm
    simpa [HLinked2.answered] using ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))
  | @refuse R R' m c _ _ ih =>
    obtain ⟨k', ws', hm⟩ := hv _ List.mem_cons_self
    subst hm
    simpa [HLinked2.answered] using ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))
  | @answer R R' m p c _ hl _ ih =>
    obtain ⟨k', ws', hm'⟩ := hv _ List.mem_cons_self
    subst hm'
    rcases p with fs | us'
    · exact absurd hl (by simp [HLinked2.hostLegal])
    · intro e he
      simp only [HLinked2.answered, List.mem_cons] at he
      rcases he with rfl | he
      · exact hl
      · exact ih (fun x hx => hv x (List.mem_cons_of_mem _ hx)) e he

/-- **The scripted host of legal answers is typed.** -/
theorem hostTyped_scriptG {S : List (Fin l.host.length × List IVal × List IVal)}
    (hS : ∀ e ∈ S, ValTy.checkList l.host[e.1].2.results e.2.2 = true) :
    l.HostTyped (HLinked2.scriptG S) := by
  intro i k hk ws rs s' h
  simp only [HLinked2.scriptG] at h
  split at h
  · rename_i k' ws' us' he
    split_ifs at h with hc
    obtain ⟨hf, -⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hk' : k = k'.val := by
      have := congrArg HostFuncId.idx hf
      simpa using this
    subst hk'
    refine ⟨us', rfl, ?_⟩
    have := hS _ (List.mem_of_getElem? he)
    simpa using this
  · cases h

/-- A scripted host refuses a call other than its next scripted one. -/
theorem scriptG_refuse {n : Nat} {S : List (Fin n × List IVal × List IVal)} {i : ℕ}
    {k : Fin n} {ws : List IVal}
    (hne : ∀ k' ws' us', S[i]? = some (k', ws', us') → (k, Payload.vals ws) ≠ (k', .vals ws')) :
    HLinked2.scriptG S i ⟨k.val⟩ (ws.map toRefVal) = none := by
  simp only [HLinked2.scriptG]
  split
  · rename_i k' ws' us' he
    refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
    rintro ⟨hf, hw⟩
    apply hne k' ws' us' he
    have hk : k = k' := Fin.ext (by simpa using congrArg HostFuncId.idx hf)
    rw [hk, map_toRefVal_inj hw]
  · rfl

theorem hostRun_scriptG_aux {S : List (Fin l.host.length × List IVal × List IVal)}
    {R R' : List (sigN l.host.length).Op} {c : List (Call (sigN l.host.length))}
    (hr : HLinked2.RealRun l.host R c R') (hv : HLinked2.ValsCalls c) :
    ∀ i, S.drop i = HLinked2.answered c →
      HostRun (HLinked2.scriptG S) i c (i + (HLinked2.answered c).length) := by
  induction hr with
  | nil => intro i _; simpa [HLinked2.answered] using HostRun.nil i
  | @forced R R' m c hF hc ih =>
    intro i hi
    obtain ⟨k, ws, hm⟩ := hv _ List.mem_cons_self
    subst hm
    have hv' : HLinked2.ValsCalls c := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hi' : S.drop i = HLinked2.answered c := by simpa [HLinked2.answered] using hi
    refine .cons ⟨k, ws, rfl, ?_⟩ (by simpa [HLinked2.answered] using ih hv' i hi')
    refine ⟨scriptG_refuse ?_, rfl⟩
    intro k' ws' us' he heq
    simp only [Prod.mk.injEq, Payload.vals.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hh : (HLinked2.answered c).head? = some (k, ws, us') := by
      rw [← hi', List.head?_drop, he]
    obtain ⟨h₁, h₂⟩ := head_answered hc hv' hh
    rcases hF with hF | hF
    · exact h₁ hF
    · exact hF ⟨us', h₂⟩
  | @refuse R R' m c hF hc ih =>
    intro i hi
    obtain ⟨k, ws, hm⟩ := hv _ List.mem_cons_self
    subst hm
    have hv' : HLinked2.ValsCalls c := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hi' : S.drop i = HLinked2.answered c := by simpa [HLinked2.answered] using hi
    refine .cons ⟨k, ws, rfl, ?_⟩ (by simpa [HLinked2.answered] using ih hv' i hi')
    refine ⟨scriptG_refuse ?_, rfl⟩
    intro k' ws' us' he heq
    simp only [Prod.mk.injEq, Payload.vals.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hh : (HLinked2.answered c).head? = some (k, ws, us') := by
      rw [← hi', List.head?_drop, he]
    exact (head_answered hc hv' hh).1 List.mem_cons_self
  | @answer R R' m p c hm hl hc ih =>
    intro i hi
    obtain ⟨k, ws, hm'⟩ := hv _ List.mem_cons_self
    subst hm'
    have hv' : HLinked2.ValsCalls c := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    rcases p with fs | us
    · exact absurd hl (by simp [HLinked2.hostLegal])
    · have hi' : S.drop (i + 1) = HLinked2.answered c := by
        rw [← List.drop_drop, hi]
        simp [HLinked2.answered]
      have hS : S[i]? = some (k, ws, us) := by
        rw [← List.head?_drop, hi]
        simp [HLinked2.answered]
      refine .cons (s₁ := i + 1) ⟨k, ws, rfl, ?_⟩ ?_
      · simp [HLinked2.scriptG, hS]
      · simpa [HLinked2.answered, Nat.add_assoc, Nat.add_comm 1] using ih hv' (i + 1) hi'

/-- **Every realizable history on IR arguments is answered by its scripted host**, from the
state `0` to the number of its answered calls. -/
theorem hostRun_scriptG {R' : List (sigN l.host.length).Op}
    {c : List (Call (sigN l.host.length))} (hr : HLinked2.RealRun l.host [] c R')
    (hv : HLinked2.ValsCalls c) :
    l.HostTyped (HLinked2.scriptG (HLinked2.answered c)) ∧
      HostRun (HLinked2.scriptG (HLinked2.answered c)) 0 c (HLinked2.answered c).length := by
  refine ⟨hostTyped_scriptG (answered_legal hr hv), ?_⟩
  simpa using hostRun_scriptG_aux (S := HLinked2.answered c) hr hv 0 (by simp)

/-! ## The obstruction -/

/-- **No host refuses a call and then answers it**, with nothing answered in between. -/
theorem not_hostRun_refuse_answer {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) {n : Nat} {s s' : σ}
    {m : (sigN n).Op} {p : Payload} :
    ¬ HostRun g s [⟨m, none⟩, ⟨m, some p⟩] s' := by
  intro h
  cases h with
  | cons h₁ h =>
    cases h with
    | cons h₂ _ =>
      obtain ⟨k, ws, hm, hg, rfl⟩ := h₁
      obtain ⟨k', ws', hm', hA⟩ := h₂
      simp only at hm hm'
      rw [hm] at hm'
      simp only [Prod.mk.injEq, Payload.vals.injEq] at hm'
      obtain ⟨rfl, rfl⟩ := hm'
      rcases p with fs | us
      · exact hA
      · simp only at hA
        rw [hg] at hA
        cases hA

/-- **No realizable history refuses a call and then answers it.** -/
theorem not_realRun_refuse_answer {h : Iface} {R R' : List (sigN h.length).Op}
    {m : (sigN h.length).Op} {p : Payload} :
    ¬ HLinked2.RealRun h R [⟨m, none⟩, ⟨m, some p⟩] R' := by
  intro hr
  cases hr with
  | forced hF hr =>
    cases hr with
    | answer hm hl _ =>
      rcases hF with hF | hF
      · exact hm hF
      · rcases p with fs | us
        · exact absurd hl (by simp [HLinked2.hostLegal])
        · exact hF ⟨us, hl⟩
  | refuse _ hr =>
    cases hr with
    | answer hm _ _ => exact hm List.mem_cons_self

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
