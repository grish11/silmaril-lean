module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Ret

/-!
# The transfer of a finished round

`Inv` and `ret_transfer` (see `Ret`).
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

theorem visRun_split {h : Iface} :
    ∀ {R R₂ : List (sigN h.length).Op} {A B : List (Call (sigN h.length))},
      HLinked2.VisRun h R (A ++ B) R₂ → ∃ R₁, HLinked2.VisRun h R A R₁ ∧ HLinked2.VisRun h R₁ B R₂
  | R, _, [], _, hr => ⟨R, .nil R, hr⟩
  | _, _, _ :: A, _, hr => by
    cases hr with
    | refuse hF hr =>
      obtain ⟨R₁, h₁, h₂⟩ := visRun_split hr
      exact ⟨R₁, .refuse hF h₁, h₂⟩
    | answer hm hl hr =>
      obtain ⟨R₁, h₁, h₂⟩ := visRun_split hr
      exact ⟨R₁, .answer hm hl h₁, h₂⟩

theorem singleton_append_inj {α : Type} {A B : List α} {x y : α} (h : A ++ [x] = B ++ [y]) :
    A = B ∧ x = y := by
  have := List.append_inj' h rfl
  simpa using this

/-- The relation of the bisimulation: states reached by sessions of the same calls and outcomes
whose host calls are realizable histories with the same answered calls and refusals. -/
def Inv (X : HLinked2) (IeX IiX : SInst) (eY : Simple) (iY : SimpleI) (wY : List Nat)
    (IeY IiY : SInst) (len : X.imp.exports.length = iY.exports.length) (o : GrowOracle)
    (sX sY : X.St) : Prop :=
  sX.2.2 = sY.2.2 ∧ ∃ (callsX : List (Fin X.imp.exports.length × List IVal))
    (outs : List (Option (List IVal))) (hsX hsY : List (List (Call (sigN X.host.length)))),
    SimpleI.TypedCalls X.imp callsX ∧
    HLinked2.SessSpec (profile o) X IeX IiX IiX.store IeX.store callsX outs hsX sX.1 sX.2.1 ∧
    HLinked2.SessSpec (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY IiY.store IeY.store
      (Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len callsX) outs hsY sY.1 sY.2.1 ∧
    HLinked2.RealRun X.host [] hsX.flatten sX.2.2 ∧ HLinked2.RealRun X.host [] hsY.flatten sX.2.2 ∧
    HLinked2.ValsCalls hsX.flatten ∧ HLinked2.ValsCalls hsY.flatten ∧
    HLinked2.answered hsX.flatten = HLinked2.answered hsY.flatten

/-- The same finite observations under every scripted host. -/
def ObsSame (X : HLinked2) (IeX IiX : SInst) (eY : Simple) (iY : SimpleI) (wY : List Nat)
    (IeY IiY : SInst) (len : X.imp.exports.length = iY.exports.length) (o : GrowOracle) : Prop :=
  ∀ callsX : List (Fin X.imp.exports.length × List IVal), SimpleI.TypedCalls X.imp callsX →
    ∀ S : List (Fin X.host.length × List IVal × List IVal), X.HostTyped (HLinked2.scriptG S) →
      SObs (profile o) X IeX IiX callsX (HLinked2.scriptG S) 0 =
        SObs (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY
          (Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len callsX) (HLinked2.scriptG S) 0

variable {X : HLinked2} {IeX IiX : SInst} {eY : Simple} {iY : SimpleI} {wY : List Nat}
  {IeY IiY : SInst} {o : GrowOracle}

theorem castCalls_snoc (len : X.imp.exports.length = iY.exports.length)
    (calls : List (Fin X.imp.exports.length × List IVal)) (q : Fin X.imp.exports.length × List IVal) :
    Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len (calls ++ [q]) =
      Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len calls ++ [(Fin.cast len q.1, q.2)] := by
  simp [Linked2.castCalls]

theorem typedCalls_snoc {calls : List (Fin X.imp.exports.length × List IVal)}
    {q : Fin X.imp.exports.length × List IVal} (ht : SimpleI.TypedCalls X.imp calls)
    (hq : ValTy.checkList X.imp.exports[q.1].ty.params q.2 = true) :
    SimpleI.TypedCalls X.imp (calls ++ [q]) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact ht x hx
  · simp only [List.mem_singleton] at hx; subst hx; exact hq

/-- **A finished behaviour transfers along `Inv`.** -/
theorem ret_transfer (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (hobs : ObsSame X IeX IiX eY iY wY IeY IiY len o) {sX sY : X.St}
    (hI : Inv X IeX IiX eY iY wY IeY IiY len o sX sY) {a : Nat × Payload}
    {c : List (Call (sigN X.host.length))} {b : Payload ⊕ PUnit.{1}} {sX₁ : X.St}
    (hc : (c, End.ret b sX₁) ∈ HLinked2.compFin (profile o) X IeX IiX sX a) :
    ∃ sY₁ : X.St, (c, End.ret b sY₁) ∈
        HLinked2.compFin (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY sY a ∧
      Inv X IeX IiX eY iY wY IeY IiY len o sX₁ sY₁ := by
  obtain ⟨uX, πX, R⟩ := sX
  obtain ⟨uY, πY, R'⟩ := sY
  obtain ⟨hRR, callsX, outs, hsX, hsY, ht, hX, hY, hRX, hRY, hvX, hvY, hans⟩ := hI
  simp only at hRR hX hY hRX hRY
  subst hRR
  have hqY := LinkedSessionEquiv.typedQ_castL hty a
  cases hq : X.toL2.typedQ a with
  | none =>
    rw [hq] at hqY
    simp only [HLinked2.compFin, hq, Set.mem_singleton_iff, Prod.mk.injEq, End.ret.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    refine ⟨(uY, πY, R), ?_, rfl, callsX, outs, hsX, hsY, ht, hX, hY, hRX, hRY, hvX, hvY, hans⟩
    simp only [HLinked2.compFin]
    rw [hqY]
    rfl
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    rw [hq] at hqY
    simp only [Option.map_some] at hqY
    have htj := (LinkedSessionEquiv.typedQ_some hq).2
    simp only [HLinked2.compFin, hq] at hc
    -- the actual round of `X`
    have key : ∃ (Hx : List (Call (sigN X.host.length))) (o₀ : Option (List IVal)) (uX' πX' : Store Nat)
        (R₁ : List (sigN X.host.length).Op),
        HLinked2.SessSpec (profile o) X IeX IiX uX πX [(j, vs)] [o₀] [Hx] uX' πX' ∧
        HLinked2.RealRun X.host R Hx R₁ ∧ sX₁ = (uX', πX', R₁) ∧
        ((Hx = c ∧ HLinked2.VisRun X.host R c R₁ ∧ b = outAns o₀) ∨
          ∃ m, Hx = c ++ [⟨m, none⟩] ∧ HLinked2.VisRun X.host R c R₁ ∧
            HLinked2.Forced X.host R₁ m ∧ b = .inr PUnit.unit) := by
      rcases hc with ⟨o₀, u', π', R₁, hs, hv, he⟩ | ⟨m, u', π', R₁, hs, hv, hF, he⟩ | ⟨_, _, _, he⟩
      · simp only [End.ret.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨c, o₀, u', π', R₁, hs, visRun_realRun hv, rfl, .inl ⟨rfl, hv, rfl⟩⟩
      · simp only [End.ret.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨_, none, u', π', R₁, hs, realRun_append (visRun_realRun hv) (.forced hF (.nil _)),
          rfl, .inr ⟨m, rfl, hv, hF, rfl⟩⟩
      · cases he
    obtain ⟨Hx, o₀, uX', πX', R₁, rX, hRx, rfl, hcase⟩ := key
    clear hc
    -- the script of the history and the round
    have hRXH : HLinked2.RealRun X.host [] (hsX.flatten ++ Hx) R₁ := realRun_append hRX hRx
    have hvHx : HLinked2.ValsCalls Hx := valsCalls_round rX
    have hvXH : HLinked2.ValsCalls (hsX.flatten ++ Hx) := valsCalls_append hvX hvHx
    obtain ⟨hTy, hRunX⟩ := hostRun_scriptG hRXH hvXH
    set S := HLinked2.answered (hsX.flatten ++ Hx) with hSdef
    have hXs := sessSpecH_append hX rX
    have ht' := typedCalls_snoc (q := (j, vs)) ht htj
    have hobsX : (outs ++ [o₀], (S.length, [] ++ evs (hsX.flatten ++ Hx))) ∈
        SObs (profile o) X IeX IiX (callsX ++ [(j, vs)]) (HLinked2.scriptG S) 0 :=
      ⟨hsX ++ [Hx], uX', πX', hXs, by simpa using hostRun_logG hRunX []⟩
    rw [hobs _ ht' S hTy, castCalls_snoc] at hobsX
    obtain ⟨hs', uY', πY', hYs, hR'⟩ := hobsX
    obtain ⟨outs₁, o', hs₁, H', ub, πb, hout, rfl, hpre, hlast⟩ := sessSpecH_append_inv hYs
    obtain ⟨hRun', hlog⟩ := hostRun_of_logG hR'
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil] at hRun' hlog
    obtain ⟨n₂, hR₁', hR₂'⟩ := hostRun_append.1 hRun'
    -- the history of `Y` under the script
    have hRYH : HLinked2.RealRun X.host [] (hsY.flatten ++ Hx) R₁ := realRun_append hRY hRx
    have hSY : HLinked2.answered (hsY.flatten ++ Hx) = S := by
      rw [hSdef, answered_append, answered_append, hans]
    obtain ⟨-, hRunY⟩ := hostRun_scriptG hRYH (valsCalls_append hvY hvHx)
    rw [hSY] at hRunY
    obtain ⟨n₁, hY₁, hY₂⟩ := hostRun_append.1 hRunY
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := sess_unique _ _ hY hY₁ hpre hR₁'
    obtain ⟨-, ho⟩ := singleton_append_inj hout
    subst ho
    -- the same answered calls
    have hev : evs (hsX.flatten ++ Hx) = evs (hsY.flatten ++ H') := by simpa using hlog
    have hanH : HLinked2.answered Hx = HLinked2.answered H' := by
      have := answered_of_evs hev
      rw [answered_append, answered_append, hans] at this
      exact List.append_cancel_left this
    -- shapes
    obtain ⟨Ax, Tx, rfl, hAx, hTx⟩ := round_shape rX (hostRun_forms hY₂)
    obtain ⟨Ay, Ty, rfl, hAy, hTy'⟩ := round_shape (l := ⟨eY, iY, wY, X.host⟩) hlast
      (hostRun_forms hR₂')
    rw [answered_allAns_append hTx, answered_allAns_append hTy'] at hanH
    obtain rfl := allAns_eq hAx hAy hanH
    obtain ⟨RA, hRA, hRT⟩ := realRun_split hRx
    -- the two probes
    have probeXY : ∀ {m : (sigN X.host.length).Op} {T : List (Call (sigN X.host.length))},
        Tx = [⟨m, none⟩] → Ty = T → ¬ HLinked2.Forced X.host RA m →
        (T = [] ∨ ∃ mY, T = [⟨mY, none⟩] ∧ mY ≠ m) → False := by
      rintro m T rfl rfl hm hT
      exact probe hX hY hRX hRY hvX hvY hans rX hlast hRA hm hT (fun S' hS' => by
        rw [hobs _ ht' S' hS', castCalls_snoc])
    have probeYX : ∀ {m : (sigN X.host.length).Op} {T : List (Call (sigN X.host.length))},
        Ty = [⟨m, none⟩] → Tx = T → ¬ HLinked2.Forced X.host RA m →
        (T = [] ∨ ∃ mY, T = [⟨mY, none⟩] ∧ mY ≠ m) → False := by
      rintro m T rfl rfl hm hT
      exact probe (X := ⟨eY, iY, wY, X.host⟩) (eY := X.exp) (iY := X.imp) (wY := X.wire) hY hX hRY
        hRX hvY hvX hans.symm hlast rX hRA hm hT (fun S' hS' => by
          rw [hobs _ ht' S' hS', castCalls_snoc])
    -- the round of `Y` as a behaviour, given its refusals
    have hrefuse : ∀ {m : (sigN X.host.length).Op} {H : List (Call (sigN X.host.length))},
        H = Ax ++ [⟨m, none⟩] → HLinked2.SessSpec (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY uY πY
          [(Fin.cast len j, vs)] [o₀] [H] uY' πY' → o₀ = none := by
      rintro m H rfl r
      exact (refuse_last r rfl).2
    have hrefuseX : ∀ {m : (sigN X.host.length).Op}, Tx = [⟨m, none⟩] → o₀ = none := by
      rintro m rfl
      exact (refuse_last rX rfl).2
    have hInv : ∀ R₂, HLinked2.RealRun X.host R (Ax ++ Ty) R₂ → R₁ = R₂ →
        Inv X IeX IiX eY iY wY IeY IiY len o (uX', πX', R₁) (uY', πY', R₂) := by
      rintro R₂ hR2 rfl
      refine ⟨rfl, callsX ++ [(j, vs)], outs ++ [o₀], hsX ++ [Ax ++ Tx], hsY ++ [Ax ++ Ty], ht', hXs,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [castCalls_snoc]; exact sessSpecH_append hY hlast
      · simpa using hRXH
      · simpa using realRun_append hRY hR2
      · simpa using hvXH
      · simpa using valsCalls_append hvY (valsCalls_round (l := ⟨eY, iY, wY, X.host⟩) hlast)
      · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
          answered_append, hans, answered_allAns_append hTx, answered_allAns_append hTy']
    have hmemN : ∀ {c' : List (Call (sigN X.host.length))}, Ax ++ Ty = c' →
        HLinked2.VisRun X.host R c' R₁ →
        (c', End.ret (outAns o₀) (uY', πY', R₁)) ∈
          HLinked2.compFin (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY (uY, πY, R) a := by
      rintro c' rfl hv
      simp only [HLinked2.compFin, hqY]
      exact .inl ⟨o₀, uY', πY', R₁, hlast, hv, rfl⟩
    have hmemF : ∀ {m : (sigN X.host.length).Op}, Ty = [⟨m, none⟩] → o₀ = none →
        HLinked2.VisRun X.host R Ax R₁ → HLinked2.Forced X.host R₁ m →
        (Ax, End.ret (.inr PUnit.unit) (uY', πY', R₁)) ∈
          HLinked2.compFin (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY (uY, πY, R) a := by
      rintro m rfl ho hv hF
      subst ho
      simp only [HLinked2.compFin, hqY]
      exact .inr (.inl ⟨m, uY', πY', R₁, hlast, hv, hF, rfl⟩)
    rcases hTx with rfl | ⟨m, rfl⟩
    · -- `X` makes no refusal
      have hRA1 : RA = R₁ := by cases hRT; rfl
      subst hRA1
      rcases hcase with ⟨hcx, hv, rfl⟩ | ⟨m, hcx, -, -, -⟩
      · simp only [List.append_nil] at hcx
        subst hcx
        rcases hTy' with rfl | ⟨m', rfl⟩
        · refine ⟨(uY', πY', RA), hmemN (by simp) (by simpa using hv), hInv RA (by simpa using hRA) rfl⟩
        · by_cases hF : HLinked2.Forced X.host RA m'
          · have ho := hrefuse rfl hlast
            subst ho
            refine ⟨(uY', πY', RA), hmemF rfl rfl (by simpa using hv) hF,
              hInv RA (realRun_append hRA (.forced hF (.nil _))) rfl⟩
          · exact (probeYX rfl rfl hF (.inl rfl)).elim
      · have hmem : (⟨m, none⟩ : Call (sigN X.host.length)) ∈ Ax ++ [] := by rw [hcx]; simp
        have := hAx ⟨m, none⟩ (by simpa using hmem)
        obtain ⟨_, _, _, he⟩ := this
        cases he
    · -- `X` refuses `m` after `Ax`
      have ho := hrefuseX rfl
      subst ho
      rcases hcase with ⟨rfl, hv, rfl⟩ | ⟨m₀, hcx, hv, hF, rfl⟩
      · -- a visible refusal: not forced
        obtain ⟨RA', hv₁, hv₂⟩ := visRun_split hv
        obtain rfl := realRun_det hRA (visRun_realRun hv₁)
        cases hv₂ with
        | refuse hnF hnil =>
          cases hnil
          rcases hTy' with rfl | ⟨m', rfl⟩
          · exact (probeXY rfl rfl hnF (.inl rfl)).elim
          · by_cases hmm : m' = m
            · subst hmm
              exact ⟨(uY', πY', m' :: RA), hmemN rfl hv, hInv _ hRx rfl⟩
            · exact (probeXY rfl rfl hnF (.inr ⟨m', rfl, hmm⟩)).elim
      · -- a hidden forced refusal
        obtain ⟨rfl, hmm⟩ := singleton_append_inj hcx
        obtain rfl : m = m₀ := by cases hmm; rfl
        obtain rfl := realRun_det hRA (visRun_realRun hv)
        rcases hTy' with rfl | ⟨m', rfl⟩
        · refine ⟨(uY', πY', RA), hmemN (by simp) (by simpa using hv), hInv RA (by simpa using hRA) rfl⟩
        · by_cases hmm : m' = m
          · subst hmm
            exact ⟨(uY', πY', RA), hmemF rfl rfl hv hF, hInv _ hRx rfl⟩
          · by_cases hF' : HLinked2.Forced X.host RA m'
            · exact ⟨(uY', πY', RA), hmemF rfl rfl hv hF',
                hInv RA (realRun_append hRA (.forced hF' (.nil _))) rfl⟩
            · exact (probeYX rfl rfl hF' (.inr ⟨m, rfl, fun h => hmm h.symm⟩)).elim

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
