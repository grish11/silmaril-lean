module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Engine
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Bisim

/-!
# Probing a refused host call

The finite observations of a linked component under the scripted hosts (`SObs`) see answered
calls only. A refused call that is not a forced refusal is still seen, by a probe: the scripted
host of the history followed by that call answered (`probe`). If one component's round refuses
the call `m` after the visible calls `A`, and the other's round, after `A`, does not ask `m`, then
under the probe the second component's session is unchanged and finishes, while the first
answers `m` and so logs one more call.
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

/-! ## Histories -/

theorem realRun_append {h : Iface} {R R₁ R₂ : List (sigN h.length).Op}
    {A B : List (Call (sigN h.length))} (hA : HLinked2.RealRun h R A R₁)
    (hB : HLinked2.RealRun h R₁ B R₂) : HLinked2.RealRun h R (A ++ B) R₂ := by
  induction hA with
  | nil => exact hB
  | forced hF _ ih => exact .forced hF (ih hB)
  | refuse hF _ ih => exact .refuse hF (ih hB)
  | answer hm hl _ ih => exact .answer hm hl (ih hB)

theorem visRun_realRun {h : Iface} {R R' : List (sigN h.length).Op}
    {c : List (Call (sigN h.length))} (hv : HLinked2.VisRun h R c R') :
    HLinked2.RealRun h R c R' := by
  induction hv with
  | nil => exact .nil _
  | refuse hF _ ih => exact .refuse hF ih
  | answer hm hl _ ih => exact .answer hm hl ih

theorem valsCalls_append {n : Nat} {A B : List (Call (sigN n))} (hA : HLinked2.ValsCalls A)
    (hB : HLinked2.ValsCalls B) : HLinked2.ValsCalls (A ++ B) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hA x hx
  · exact hB x hx

theorem valsCalls_of_append_left {n : Nat} {A B : List (Call (sigN n))}
    (h : HLinked2.ValsCalls (A ++ B)) : HLinked2.ValsCalls A :=
  fun x hx => h x (List.mem_append_left _ hx)

variable {l : HLinked2} {Ie Ii : SInst}

theorem valsCalls_impRel {c : Σ e : Ii.E.Op, Ii.E.Ar e}
    {ds : List (Call (sigN l.imp.imports.length))}
    (h : Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii c ds) :
    HLinked2.ValsCalls (l.hostCalls ds) := by
  obtain ⟨e, n⟩ := c
  obtain ⟨nm, ft, A, hi, hA, hm⟩ := h
  simp only at hm
  revert hm
  cases liftArgs ft.params (e.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat?) with
  | none => rintro ⟨-, rfl⟩; intro x hx; cases hx
  | some ws =>
    rintro ⟨hk, R, rfl, -⟩
    intro x hx
    cases hc : l.hostCall? ⟨(⟨e.1.val, hk⟩, .vals ws), R⟩ with
    | none => simp [HLinked2.hostCalls, hc] at hx
    | some y =>
      simp only [HLinked2.hostCalls, List.filterMap_cons, hc, List.filterMap_nil,
        List.mem_singleton] at hx
      subst hx
      simp only [HLinked2.hostCall?] at hc
      split at hc
      · cases hc; exact ⟨_, ws, rfl⟩
      · cases hc

theorem valsCalls_forall₂ :
    ∀ {cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)} {dss : List (List (Call (sigN l.imp.imports.length)))},
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss →
      HLinked2.ValsCalls (l.hostCalls dss.flatten)
  | [], [], .nil => fun _ h => by cases h
  | _ :: _, _ :: _, .cons h hr => by
    rw [List.flatten_cons, hostCalls_append]
    exact valsCalls_append (valsCalls_impRel h) (valsCalls_forall₂ hr)

theorem valsCalls_round {P : Profile} {u π u' π' : Store Nat} {q : Fin l.imp.exports.length × List IVal}
    {o : Option (List IVal)} {H : List (Call (sigN l.host.length))}
    (h : HLinked2.SessSpec P l Ie Ii u π [q] [o] [H] u' π') : HLinked2.ValsCalls H := by
  obtain ⟨d, -, -, ⟨xs, -, -, -, hrel⟩, -, -, -, rfl⟩ := sessSpec_singleH h
  exact valsCalls_forall₂ hrel

theorem sessSpecH_append {P : Profile} :
    ∀ {calls : List (Fin l.imp.exports.length × List IVal)} {u₀ π₀ u π u₁ π₁ : Store Nat}
      {outs : List (Option (List IVal))} {hs : List (List (Call (sigN l.host.length)))}
      {q : Fin l.imp.exports.length × List IVal} {o : Option (List IVal)}
      {H : List (Call (sigN l.host.length))},
      HLinked2.SessSpec P l Ie Ii u₀ π₀ calls outs hs u π →
      HLinked2.SessSpec P l Ie Ii u π [q] [o] [H] u₁ π₁ →
      HLinked2.SessSpec P l Ie Ii u₀ π₀ (calls ++ [q]) (outs ++ [o]) (hs ++ [H]) u₁ π₁
  | [], _, _, _, _, _, _, _, _, _, _, _, h, h' => by
    obtain ⟨rfl, rfl, rfl, rfl⟩ := sessSpecH_nil_inv h
    exact h'
  | q₀ :: calls, _, _, _, _, _, _, _, _, _, _, _, h, h' => by
    obtain ⟨o₀, os, H₀, hs₁, ua, πa, rfl, rfl, ha, hb⟩ := sessSpecH_cons_inv h
    exact sessSpecH_cons ha (sessSpecH_append hb h')

theorem sessSpecH_append_inv {P : Profile} :
    ∀ {calls : List (Fin l.imp.exports.length × List IVal)} {u₀ π₀ u₁ π₁ : Store Nat}
      {outs : List (Option (List IVal))} {hs : List (List (Call (sigN l.host.length)))}
      {q : Fin l.imp.exports.length × List IVal},
      HLinked2.SessSpec P l Ie Ii u₀ π₀ (calls ++ [q]) outs hs u₁ π₁ →
      ∃ outs₁ o hs₁ H u π, outs = outs₁ ++ [o] ∧ hs = hs₁ ++ [H] ∧
        HLinked2.SessSpec P l Ie Ii u₀ π₀ calls outs₁ hs₁ u π ∧
        HLinked2.SessSpec P l Ie Ii u π [q] [o] [H] u₁ π₁
  | [], u₀, π₀, _, _, _, _, _, h => by
    obtain ⟨o, os, H, hs₁, ua, πa, rfl, rfl, ha, hb⟩ := sessSpecH_cons_inv h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := sessSpecH_nil_inv hb
    exact ⟨[], o, [], H, u₀, π₀, rfl, rfl, .nil _ _, ha⟩
  | q₀ :: calls, _, _, _, _, _, _, _, h => by
    obtain ⟨o₀, os, H₀, hs₁, ua, πa, rfl, rfl, ha, hb⟩ := sessSpecH_cons_inv h
    obtain ⟨outs₁, o, hs₂, H, u, π, rfl, rfl, h₁, h₂⟩ := sessSpecH_append_inv hb
    exact ⟨o₀ :: outs₁, o, H₀ :: hs₂, H, u, π, rfl, rfl, sessSpecH_cons ha h₁, h₂⟩

/-! ## Observations under a host -/

/-- **The finite observations of `calls` under the logging host of `g` from `s₀`**, at fixed
instances: the outcomes, and the host state and log. -/
def SObs (P : Profile) (l : HLinked2) (Ie Ii : SInst)
    (calls : List (Fin l.imp.exports.length × List IVal)) {τ : Type}
    (g : τ → HostFuncId → List RVal → Option (List RVal × τ)) (s₀ : τ) :
    Set (List (Option (List IVal)) × (τ × List HLinked2.HostEvent)) :=
  {p | ∃ hs u π, HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls p.1 hs u π ∧
    HostRun (HLinked2.logG g) (s₀, []) hs.flatten p.2}

/-! ## The probe -/

theorem hostSame_extend {n : Nat} {τ : Type} {g : τ → HostFuncId → List RVal → Option (List RVal × τ)} :
    ∀ (A : List (Call (sigN n))) {x y : Call (sigN n)} {H : List (Call (sigN n))} {i j k : τ},
      HostSame (A ++ [x]) H → HostRun g i H j → HostRun g i (A ++ [y]) k → y.1 = x.1 →
      ∃ rest, H = A ++ y :: rest
  | [], x, y, H, i, j, k, hs, hr, hr', he => by
    rcases H with _ | ⟨b, rest⟩
    · exact hs.elim
    · obtain ⟨hxb, -⟩ := hs
      cases hr with
      | cons hb _ =>
        cases hr' with
        | cons hy _ =>
          obtain ⟨h2, -⟩ := hostAnswersS_det hb hy (hxb.symm.trans he.symm)
          obtain ⟨b1, b2⟩ := b
          obtain ⟨y1, y2⟩ := y
          simp only at hxb he h2
          subst h2
          obtain rfl : b1 = y1 := hxb.symm.trans he.symm
          exact ⟨rest, rfl⟩
  | a :: A, x, y, H, i, j, k, hs, hr, hr', he => by
    rcases H with _ | ⟨b, rest⟩
    · exact hs.elim
    · obtain ⟨hab, hs'⟩ := hs
      cases hr with
      | cons hb hr =>
        cases hr' with
        | cons ha hr' =>
          obtain ⟨h2, rfl⟩ := hostAnswersS_det ha hb hab
          obtain ⟨rest', rfl⟩ := hostSame_extend A (hs' h2) hr hr' he
          obtain ⟨a1, a2⟩ := a
          obtain ⟨b1, b2⟩ := b
          simp only at hab h2
          subst hab h2
          exact ⟨rest', rfl⟩

theorem length_evs_lt {n : Nat} {A rest : List (Call (sigN n))} {k : Fin n} {ws us : List IVal} :
    (evs A).length < (evs (A ++ ⟨(k, .vals ws), some (.vals us)⟩ :: rest)).length := by
  have e : HLinked2.answered (A ++ ⟨(k, .vals ws), some (.vals us)⟩ :: rest) =
      HLinked2.answered A ++ (k, ws, us) :: HLinked2.answered rest := by
    rw [answered_append]; rfl
  simp only [evs, List.length_map, e, List.length_append, List.length_cons]
  omega

theorem length_evs_le {n : Nat} {A : List (Call (sigN n))} {m : (sigN n).Op} :
    (evs (A ++ [⟨m, none⟩])).length = (evs A).length := by
  simp [evs, answered_append, HLinked2.answered]


theorem evs_length_of_answered {n : Nat} {H K : List (Call (sigN n))}
    (h : HLinked2.answered H = HLinked2.answered K) : (evs H).length = (evs K).length := by
  simp [evs, h]

/-- **The probe**: if the round of `X` refuses `m`, not a forced refusal, after the visible calls
`A`, and the round of `Y` from a state reached by the same visible history does not ask `m`
after `A`, then some scripted host separates their finite observations. -/
theorem probe {X : HLinked2} {IeX IiX : SInst} {eY : Simple} {iY : SimpleI} {wY : List Nat}
    {IeY IiY : SInst} {o : GrowOracle}
    {callsX : List (Fin X.imp.exports.length × List IVal)}
    {callsY : List (Fin iY.exports.length × List IVal)}
    {outsX outsY : List (Option (List IVal))}
    {hsX hsY : List (List (Call (sigN X.host.length)))} {uX πX uY πY : Store Nat}
    {R RA : List (sigN X.host.length).Op}
    (hX : HLinked2.SessSpec (profile o) X IeX IiX IiX.store IeX.store callsX outsX hsX uX πX)
    (hY : HLinked2.SessSpec (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY IiY.store IeY.store callsY
      outsY hsY uY πY)
    (hRX : HLinked2.RealRun X.host [] hsX.flatten R) (hRY : HLinked2.RealRun X.host [] hsY.flatten R)
    (hvX : HLinked2.ValsCalls hsX.flatten) (hvY : HLinked2.ValsCalls hsY.flatten)
    (hans : HLinked2.answered hsX.flatten = HLinked2.answered hsY.flatten)
    {qX : Fin X.imp.exports.length × List IVal} {qY : Fin iY.exports.length × List IVal}
    {oX oY : Option (List IVal)} {A T : List (Call (sigN X.host.length))}
    {m : (sigN X.host.length).Op} {uX' πX' uY' πY' : Store Nat}
    (rX : HLinked2.SessSpec (profile o) X IeX IiX uX πX [qX] [oX] [A ++ [⟨m, none⟩]] uX' πX')
    (rY : HLinked2.SessSpec (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY uY πY [qY] [oY] [A ++ T]
      uY' πY')
    (hRA : HLinked2.RealRun X.host R A RA) (hm : ¬ HLinked2.Forced X.host RA m)
    (hT : T = [] ∨ ∃ mY, T = [⟨mY, none⟩] ∧ mY ≠ m)
    (hobs : ∀ S : List (Fin X.host.length × List IVal × List IVal),
      X.HostTyped (HLinked2.scriptG S) →
      SObs (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY (callsY ++ [qY]) (HLinked2.scriptG S) 0 ⊆
        SObs (profile o) X IeX IiX (callsX ++ [qX]) (HLinked2.scriptG S) 0) : False := by
  obtain ⟨us, hus⟩ : HLinked2.Answerable X.host m := by
    by_contra hc; exact hm (.inr hc)
  have hmR : m ∉ RA := fun h => hm (.inl h)
  have hvA : HLinked2.ValsCalls (A ++ [⟨m, none⟩]) := valsCalls_round rX
  have hvT : HLinked2.ValsCalls (A ++ T) := valsCalls_round (l := ⟨eY, iY, wY, X.host⟩) rY
  have hvy : HLinked2.ValsCalls [(⟨m, some (.vals us)⟩ : Call (sigN X.host.length))] := by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    obtain ⟨k, ws, hk⟩ := hvA ⟨m, none⟩ (by simp)
    exact ⟨k, ws, hk⟩
  have hyR : ∀ R', m ∉ R' →
      HLinked2.RealRun X.host R' [(⟨m, some (.vals us)⟩ : Call (sigN X.host.length))] [] :=
    fun R' h => .answer h hus (.nil _)
  -- the two realizable histories, and their script
  have hRXy : HLinked2.RealRun X.host [] (hsX.flatten ++ (A ++ [⟨m, some (.vals us)⟩])) [] :=
    realRun_append hRX (realRun_append hRA (hyR RA hmR))
  have hTans : HLinked2.answered T = [] := by
    rcases hT with rfl | ⟨mY, rfl, -⟩
    · rfl
    · exact answered_cons_none _ _
  have hRYy : HLinked2.RealRun X.host [] ((hsY.flatten ++ (A ++ T)) ++ [⟨m, some (.vals us)⟩]) [] := by
    rw [List.append_assoc, List.append_assoc]
    refine realRun_append hRY (realRun_append hRA ?_)
    rcases hT with rfl | ⟨mY, rfl, hne⟩
    · exact hyR RA hmR
    · by_cases hF : HLinked2.Forced X.host RA mY
      · exact .forced hF (hyR RA hmR)
      · refine .refuse hF (hyR (mY :: RA) ?_)
        intro hin
        rcases List.mem_cons.1 hin with h | h
        · exact hne h.symm
        · exact hmR h
  have hvXy : HLinked2.ValsCalls (hsX.flatten ++ (A ++ [⟨m, some (.vals us)⟩])) :=
    valsCalls_append hvX (valsCalls_append (valsCalls_of_append_left hvA) hvy)
  have hvYy : HLinked2.ValsCalls ((hsY.flatten ++ (A ++ T)) ++ [⟨m, some (.vals us)⟩]) :=
    valsCalls_append (valsCalls_append hvY hvT) hvy
  have hS : HLinked2.answered (hsX.flatten ++ (A ++ [⟨m, some (.vals us)⟩])) =
      HLinked2.answered ((hsY.flatten ++ (A ++ T)) ++ [⟨m, some (.vals us)⟩]) := by
    simp only [answered_append, hans, hTans, List.nil_append, List.append_assoc]
  set S := HLinked2.answered ((hsY.flatten ++ (A ++ T)) ++ [⟨m, some (.vals us)⟩]) with hSdef
  -- the observation of `Y` under the probe
  obtain ⟨hT', hRunY⟩ := hostRun_scriptG_prefix hRYy hvYy
  have hYs := sessSpecH_append hY rY
  have hflY : (hsY ++ [A ++ T]).flatten = hsY.flatten ++ (A ++ T) := by simp
  have hobsY : (outsY ++ [oY], ((HLinked2.answered (hsY.flatten ++ (A ++ T))).length,
      [] ++ evs (hsY.flatten ++ (A ++ T)))) ∈
      SObs (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY (callsY ++ [qY]) (HLinked2.scriptG S) 0 :=
    ⟨hsY ++ [A ++ T], uY', πY', hYs, by rw [hflY]; exact hostRun_logG hRunY []⟩
  obtain ⟨hs', u', π', hXs, hRX'⟩ := hobs S hT' hobsY
  -- the session of `X` under the probe
  obtain ⟨outs₁, o', hs₁, H', ub, πb, -, rfl, hpre, hlast⟩ := sessSpecH_append_inv hXs
  obtain ⟨hRun', hlog⟩ := hostRun_of_logG hRX'
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil] at hRun' hlog
  obtain ⟨n₂, hR₁, hR₂⟩ := hostRun_append.1 hRun'
  obtain ⟨-, hRunX⟩ := hostRun_scriptG hRXy hvXy
  rw [hS] at hRunX
  obtain ⟨n₁, hX₁, hX₂⟩ := hostRun_append.1 hRunX
  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := sess_unique _ callsX hX hX₁ hpre hR₁
  have hsame := round_same rX hlast
  obtain ⟨rest, rfl⟩ := hostSame_extend A hsame hR₂ hX₂ rfl
  have hlen : (evs hsY.flatten).length + ((evs A).length + (evs T).length) =
      (evs (hsX.flatten ++ (A ++ ⟨m, some (.vals us)⟩ :: rest))).length := by
    have := congrArg List.length hlog
    simp only [List.nil_append, evs_append, List.length_append] at this
    exact this
  have h1 := evs_length_of_answered hans
  have h2 : (evs T).length = 0 := by
    simp [evs, hTans]
  have h4 : (evs (hsX.flatten ++ (A ++ ⟨m, some (.vals us)⟩ :: rest))).length =
      (evs hsX.flatten).length + (evs (A ++ ⟨m, some (.vals us)⟩ :: rest)).length := by
    rw [evs_append, List.length_append]
  have h3 := length_evs_lt (A := A) (rest := rest) (k := (hvA ⟨m, none⟩ (by simp)).choose)
    (ws := (hvA ⟨m, none⟩ (by simp)).choose_spec.choose) (us := us)
  have hmk : m = ((hvA ⟨m, none⟩ (by simp)).choose, .vals (hvA ⟨m, none⟩ (by simp)).choose_spec.choose) :=
    (hvA ⟨m, none⟩ (by simp)).choose_spec.choose_spec
  rw [← hmk] at h3
  omega

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
