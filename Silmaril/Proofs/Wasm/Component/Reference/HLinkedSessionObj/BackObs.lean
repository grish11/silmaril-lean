module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Back
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Sess

/-!
# Sessions and divergences read back along a bisimulation

`sess_back`: a specification session of `X` under a typed host transfers along a bisimulation of
the triples to one of `Y`, with the same outcomes and host states. Hence the finite observations
(`sessObs_sub`) and the divergences (`sessDivs_sub`) of `X` under every typed host are those of
`Y`.
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

variable {X : HLinked2} {IeX IiX : SInst} {eY : Simple} {iY : SimpleI} {wY : List Nat}
  {IeY IiY : SInst}

/-- **A session under a typed host transfers along a bisimulation.** -/
theorem sess_back {P : Profile} {τ : Type}
    {G : τ → HostFuncId → List RVal → Option (List RVal × τ)} (hT : X.HostTyped G)
    {Rel : X.St → X.St → Prop}
    (hB : IsBisim (HLinked2.compTripleS P X IeX IiX)
      (HLinked2.compTripleS P ⟨eY, iY, wY, X.host⟩ IeY IiY) Rel)
    (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len) :
    ∀ (calls : List (Fin X.imp.exports.length × List IVal)) {u π u' π' : Store Nat}
      {R : List (sigN X.host.length).Op} {st st₁ : τ} {outs : List (Option (List IVal))}
      {hs : List (List (Call (sigN X.host.length)))} {u₁ π₁ : Store Nat},
      Rel (u, π, R) (u', π', R) → Refuses G R st → SimpleI.TypedCalls X.imp calls →
      HLinked2.SessSpec P X IeX IiX u π calls outs hs u₁ π₁ → HostRun G st hs.flatten st₁ →
      ∃ (R₁ : List (sigN X.host.length).Op) (u₁' π₁' : Store Nat)
        (hs' : List (List (Call (sigN X.host.length)))),
        Rel (u₁, π₁, R₁) (u₁', π₁', R₁) ∧ Refuses G R₁ st₁ ∧
        HLinked2.SessSpec P ⟨eY, iY, wY, X.host⟩ IeY IiY u' π'
          (Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len calls) outs hs' u₁' π₁' ∧
        HostRun G st hs'.flatten st₁
  | [], _, _, u', π', R, _, _, _, _, _, _, hRel, hRef, _, h, hr => by
    obtain ⟨rfl, rfl, rfl, rfl⟩ := sessSpecH_nil_inv h
    cases hr
    exact ⟨R, u', π', [], hRel, hRef, .nil _ _, .nil _⟩
  | (j, vs) :: cs, _, _, _, _, R, _, _, _, _, _, _, hRel, hRef, ht, h, hr => by
    obtain ⟨o, os, H, hs₁, ua, πa, rfl, rfl, ha, hb⟩ := sessSpecH_cons_inv h
    rw [List.flatten_cons] at hr
    obtain ⟨sta, hra, hrb⟩ := hostRun_append.1 hr
    obtain ⟨Ra, ua', πa', H', hRela, hRefa, ha', hra'⟩ :=
      round_back hT hB len hty hRel hRef (ht _ List.mem_cons_self) ha hra
    obtain ⟨R₁, u₁', π₁', hs', hRel₁, hRef₁, hb', hrb'⟩ :=
      sess_back hT hB len hty cs hRela hRefa (fun q hq => ht q (List.mem_cons_of_mem _ hq)) hb hrb
    refine ⟨R₁, u₁', π₁', H' :: hs', hRel₁, hRef₁, sessSpecH_cons ha' hb', ?_⟩
    rw [List.flatten_cons]
    exact hostRun_append.2 ⟨sta, hra', hrb'⟩

variable {o : GrowOracle}

/-- **The finite observations transfer along a bisimulation of the initial states.** -/
theorem sessObs_sub (prof : ProfileKind) (hX : X.Adequate)
    (hY : (⟨eY, iY, wY, X.host⟩ : HLinked2).Adequate)
    (hIe : X.exp.mod.IsInst IeX) (hIi : X.imp.mod.IsInst IiX)
    (hIe' : eY.mod.IsInst IeY) (hIi' : iY.mod.IsInst IiY) {Rel : X.St → X.St → Prop}
    (hB : IsBisim (HLinked2.compTripleS (profile o) X IeX IiX)
      (HLinked2.compTripleS (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY) Rel)
    (h0 : Rel (IiX.store, IeX.store, []) (IiY.store, IeY.store, []))
    (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (calls : List (Fin X.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls X.imp calls)
    {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (hT : X.HostTyped g)
    (s₀ : σ) :
    HLinked2.sessObs (profile o) prof X g s₀ calls ⊆
      HLinked2.sessObs (profile o) prof ⟨eY, iY, wY, X.host⟩ g s₀
        (Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len calls) := by
  rintro ⟨ob, st⟩ hob
  obtain ⟨Ie₀, Ii₀, outs, hs, u, π, hIe₀, hIi₀, hS, hr, rfl⟩ :=
    HLinked2.sess_refToSpec (profile o) prof hX g hT s₀ calls ht hob
  have e1 : IeX = Ie₀ := NumModule.IsInst.unique hIe hIe₀
  have e2 : IiX = Ii₀ := ImpModule.IsInst.unique hIi hIi₀
  subst e1 e2
  obtain ⟨_, _, _, hs', _, _, hS', hr'⟩ :=
    sess_back (HLinkedSession.HostTyped.logG hT) hB len hty calls h0 (fun _ h => (List.not_mem_nil h).elim)
      ht hS hr
  exact HLinked2.sess_specToRef (profile o) prof hY g hT s₀ hIe' hIi' hS' hr'

/-- **The divergences transfer along a bisimulation of the initial states.** -/
theorem sessDivs_sub (hIe : X.exp.mod.IsInst IeX) (hIi : X.imp.mod.IsInst IiX)
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
    HLinked2.sessDivs (profile o) X g s₀ calls j vs ⊆
      HLinked2.sessDivs (profile o) ⟨eY, iY, wY, X.host⟩ g s₀
        (Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len calls) (Fin.cast len j) vs := by
  rintro ⟨outs, st'⟩ ⟨Ie₀, Ii₀, hs, u, π, st, hIe₀, hIi₀, hS, hr, hd⟩
  have e1 : IeX = Ie₀ := NumModule.IsInst.unique hIe hIe₀
  have e2 : IiX = Ii₀ := ImpModule.IsInst.unique hIi hIi₀
  subst e1 e2
  have hTG := HLinkedSession.HostTyped.logG hT
  obtain ⟨R, u', π', hs', hRel, hRef, hS', hr'⟩ :=
    sess_back hTG hB len hty calls h0 (fun _ h => (List.not_mem_nil h).elim) ht hS hr
  obtain ⟨c, hdC, hrc⟩ := roundDiv_to_C hd
  have hA : AllAns c := allAns_of_hostRun hrc (roundDivC_answered hdC)
  obtain ⟨R₁, hRR, -⟩ := realRun_of_hostRun_aux _ hTG hrc R hRef
  have hv := realRun_vis hA hRR
  have hl := visRun_legal hv
  have hq : X.toL2.typedQ (j.val, .vals vs) = some (j, vs) := LinkedSessionEquiv.typedQ_typed hvs
  have hqY := LinkedSessionEquiv.typedQ_castL hty (j.val, .vals vs)
  rw [hq] at hqY
  simp only [Option.map_some] at hqY
  have hmem : (legalize c hl, End.div) ∈
      (HLinked2.compTripleS (profile o) X IeX IiX).1 (u, π, R) (j.val, .vals vs) := by
    show ((legalize c hl).map StratLegal.liftCall, End.div) ∈
      HLinked2.compFin (profile o) X IeX IiX (u, π, R) (j.val, .vals vs)
    rw [map_liftCall_legalize]
    simp only [HLinked2.compFin, hq]
    exact .inr (.inr ⟨R₁, hdC, hv, rfl⟩)
  have hmem' := ((hB _ _ hRel).div _ _).1 hmem
  change ((legalize c hl).map StratLegal.liftCall, End.div) ∈
    HLinked2.compFin (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY (u', π', R) (j.val, .vals vs) at hmem'
  rw [map_liftCall_legalize] at hmem'
  simp only [HLinked2.compFin, hqY] at hmem'
  rcases hmem' with ⟨_, _, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, he⟩ | ⟨_, hdC', _, -⟩
  · cases he
  · cases he
  · exact ⟨IeY, IiY, hs', u', π', st, hIe', hIi', hS', hr', roundDiv_of_C hdC' hrc⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
