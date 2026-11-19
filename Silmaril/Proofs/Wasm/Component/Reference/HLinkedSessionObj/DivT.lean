module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.RetT

/-!
# The transfer of a diverging round

A diverging round makes only answered host calls (`roundDivC_no_refuse`), so the divergence
observations under the scripted host of the history and the round (`DObs`) determine it
(`div_transfer`).
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

variable {l : HLinked2} {Ie Ii : SInst}

theorem roundDiv_of_C {P : Profile} {τ : Type}
    {g : τ → HostFuncId → List RVal → Option (List RVal × τ)} {u π : Store Nat}
    {j : Fin l.imp.exports.length} {vs : List IVal} {c : List (Call (sigN l.host.length))}
    {st st' : τ} (h : HLinked2.RoundDivC P l Ie Ii u π j vs c) (hr : HostRun g st c st') :
    HLinked2.RoundDiv P l Ie Ii g u π st j vs st' := by
  obtain ⟨d, s, t, π₁, hj, hv, hok, hp, he, hc, hdiv⟩ := h
  subst hc
  exact ⟨d, s, t, π₁, hj, hv, hok, hp, he, hr, hdiv⟩

theorem roundDiv_to_C {P : Profile} {τ : Type}
    {g : τ → HostFuncId → List RVal → Option (List RVal × τ)} {u π : Store Nat}
    {j : Fin l.imp.exports.length} {vs : List IVal} {st st' : τ}
    (h : HLinked2.RoundDiv P l Ie Ii g u π st j vs st') :
    ∃ c, HLinked2.RoundDivC P l Ie Ii u π j vs c ∧ HostRun g st c st' := by
  obtain ⟨d, s, t, π₁, hj, hv, hok, hp, he, hr, hdiv⟩ := h
  exact ⟨_, ⟨d, s, t, π₁, hj, hv, hok, hp, he, rfl, hdiv⟩, hr⟩

theorem allAns_of_hostRun {τ : Type} {g : τ → HostFuncId → List RVal → Option (List RVal × τ)}
    {n : Nat} {s s' : τ} {H : List (Call (sigN n))} (h : HostRun g s H s')
    (hn : ∀ x ∈ H, x.2 ≠ none) : AllAns H := by
  intro x hx
  rcases hostRun_forms h x hx with h' | h'
  · exact (hn x hx h').elim
  · exact h'

theorem roundDivC_answered {P : Profile} {u π : Store Nat} {j : Fin l.imp.exports.length}
    {vs : List IVal} {c : List (Call (sigN l.host.length))}
    (h : HLinked2.RoundDivC P l Ie Ii u π j vs c) : ∀ x ∈ c, x.2 ≠ none := by
  intro x hx hn
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  obtain ⟨m, r⟩ := x
  simp only at hn
  subst hn
  exact roundDivC_no_refuse h rfl

/-- **The divergence observations** of `calls`, then export `j` on `vs`, under the logging host
of `g` from `s₀`, at fixed instances. -/
def DObs (P : Profile) (l : HLinked2) (Ie Ii : SInst)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) {τ : Type} (g : τ → HostFuncId → List RVal → Option (List RVal × τ))
    (s₀ : τ) : Set (List (Option (List IVal)) × (τ × List HLinked2.HostEvent)) :=
  {p | ∃ hs u π st, HLinked2.SessSpec P l Ie Ii Ii.store Ie.store calls p.1 hs u π ∧
    HostRun (HLinked2.logG g) (s₀, []) hs.flatten st ∧
    HLinked2.RoundDiv P l Ie Ii (HLinked2.logG g) u π st j vs p.2}

/-- The same divergence observations under every scripted host. -/
def DivSame (X : HLinked2) (IeX IiX : SInst) (eY : Simple) (iY : SimpleI) (wY : List Nat)
    (IeY IiY : SInst) (len : X.imp.exports.length = iY.exports.length) (o : GrowOracle) : Prop :=
  ∀ callsX : List (Fin X.imp.exports.length × List IVal), SimpleI.TypedCalls X.imp callsX →
    ∀ (j : Fin X.imp.exports.length) (vs : List IVal),
      ValTy.checkList X.imp.exports[j].ty.params vs = true →
    ∀ S : List (Fin X.host.length × List IVal × List IVal), X.HostTyped (HLinked2.scriptG S) →
      DObs (profile o) X IeX IiX callsX j vs (HLinked2.scriptG S) 0 =
        DObs (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY
          (Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len callsX) (Fin.cast len j) vs
          (HLinked2.scriptG S) 0

variable {X : HLinked2} {IeX IiX : SInst} {eY : Simple} {iY : SimpleI} {wY : List Nat}
  {IeY IiY : SInst} {o : GrowOracle}

/-- **A diverging behaviour transfers along `Inv`.** -/
theorem div_transfer (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (hdobs : DivSame X IeX IiX eY iY wY IeY IiY len o) {sX sY : X.St}
    (hI : Inv X IeX IiX eY iY wY IeY IiY len o sX sY) {a : Nat × Payload}
    {c : List (Call (sigN X.host.length))}
    (hc : (c, End.div) ∈ HLinked2.compFin (profile o) X IeX IiX sX a) :
    (c, End.div) ∈ HLinked2.compFin (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY sY a := by
  obtain ⟨uX, πX, R⟩ := sX
  obtain ⟨uY, πY, R'⟩ := sY
  obtain ⟨hRR, callsX, outs, hsX, hsY, ht, hX, hY, hRX, hRY, hvX, hvY, hans⟩ := hI
  simp only at hRR hX hY hRX hRY
  subst hRR
  have hqY := LinkedSessionEquiv.typedQ_castL hty a
  cases hq : X.toL2.typedQ a with
  | none =>
    simp [HLinked2.compFin, hq] at hc
  | some jv =>
    obtain ⟨j, vs⟩ := jv
    rw [hq] at hqY
    simp only [Option.map_some] at hqY
    have htj := (LinkedSessionEquiv.typedQ_some hq).2
    simp only [HLinked2.compFin, hq] at hc
    obtain ⟨R₁, hdiv, hv, -⟩ : ∃ R₁, HLinked2.RoundDivC (profile o) X IeX IiX uX πX j vs c ∧
        HLinked2.VisRun X.host R c R₁ ∧ True := by
      rcases hc with ⟨_, _, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, he⟩ | ⟨R₁, hd, hv, -⟩
      · cases he
      · cases he
      · exact ⟨R₁, hd, hv, trivial⟩
    have hRc := visRun_realRun hv
    -- the script
    have hRXH : HLinked2.RealRun X.host [] (hsX.flatten ++ c) R₁ := realRun_append hRX hRc
    have hvc : HLinked2.ValsCalls c := by
      obtain ⟨d, -, -, -, -, -, ⟨xs, -, -, -, hrel⟩, -, -, hcd, -⟩ := hdiv
      rw [← hcd]
      exact valsCalls_forall₂ hrel
    obtain ⟨hTy, hRunX⟩ := hostRun_scriptG hRXH (valsCalls_append hvX hvc)
    set S := HLinked2.answered (hsX.flatten ++ c) with hSdef
    obtain ⟨n₁, hX₁, hX₂⟩ := hostRun_append.1 hRunX
    have hmemX : (outs, (S.length, [] ++ evs hsX.flatten ++ evs c)) ∈
        DObs (profile o) X IeX IiX callsX j vs (HLinked2.scriptG S) 0 := by
      refine ⟨hsX, uX, πX, (n₁, [] ++ evs hsX.flatten), hX, hostRun_logG hX₁ [], ?_⟩
      exact roundDiv_of_C hdiv (hostRun_logG hX₂ _)
    rw [hdobs callsX ht j vs htj S hTy] at hmemX
    obtain ⟨hs', u', π', st, hYs, hR', hdivY⟩ := hmemX
    -- uniqueness of the history of `Y`
    have hRYH : HLinked2.RealRun X.host [] (hsY.flatten ++ c) R₁ := realRun_append hRY hRc
    have hSY : HLinked2.answered (hsY.flatten ++ c) = S := by
      rw [hSdef, answered_append, answered_append, hans]
    obtain ⟨-, hRunY⟩ := hostRun_scriptG hRYH (valsCalls_append hvY hvc)
    rw [hSY] at hRunY
    obtain ⟨m₁, hY₁, -⟩ := hostRun_append.1 hRunY
    obtain ⟨hRs', hlog₁⟩ := hostRun_of_logG hR'
    obtain ⟨-, rfl, rfl, rfl, hst⟩ := sess_unique _ _ hY hY₁ hYs hRs'
    obtain ⟨c', hdC, hrc'⟩ := roundDiv_to_C hdivY
    obtain ⟨hrc'', hlog₂⟩ := hostRun_of_logG hrc'
    -- the same host calls
    have hev : evs c' = evs c := by
      have h2 : [] ++ evs hsX.flatten ++ evs c = st.2 ++ evs c' := hlog₂
      rw [hlog₁] at h2
      have h3 : evs hsX.flatten = evs hsY.flatten := by simp [evs, hans]
      simp only [List.nil_append, h3] at h2
      exact (List.append_cancel_left h2).symm
    have hc' : c' = c := by
      refine allAns_eq ?_ ?_ (answered_of_evs hev)
      · exact allAns_of_hostRun hrc'' (roundDivC_answered (l := ⟨eY, iY, wY, X.host⟩) hdC)
      · exact allAns_of_hostRun hX₂ (roundDivC_answered (l := X) hdiv)
    subst hc'
    simp only [HLinked2.compFin, hqY]
    exact .inr (.inr ⟨R₁, hdC, hv, rfl⟩)

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
