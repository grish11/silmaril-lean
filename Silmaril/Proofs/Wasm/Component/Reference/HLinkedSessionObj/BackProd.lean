module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.BackInf
import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Sess

/-!
# Infinite sessions read back along a bisimulation

An infinite specification session of `X` under a typed host (`HLinked2.SpecSessProd`) transfers,
round by round (`round_back`, dependent choice), to one of `Y` under the same host, along the same
host-state stream (`specSessProd_sub`).
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
  {IeY IiY : SInst} {o : GrowOracle}

/-- **Infinite sessions transfer along a bisimulation of the initial states.** -/
theorem specSessProd_sub (hIe : X.exp.mod.IsInst IeX) (hIi : X.imp.mod.IsInst IiX)
    (hIe' : eY.mod.IsInst IeY) (hIi' : iY.mod.IsInst IiY) {Rel : X.St → X.St → Prop}
    (hB : IsBisim (HLinked2.compTripleS (profile o) X IeX IiX)
      (HLinked2.compTripleS (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY) Rel)
    (h0 : Rel (IiX.store, IeX.store, []) (IiY.store, IeY.store, []))
    (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (a : ℕ → Fin X.imp.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList X.imp.exports[(a k).1].ty.params (a k).2 = true)
    {σ : Type} (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (hT : X.HostTyped g)
    (s₀ : σ) (hst : ℕ → σ × List HLinked2.HostEvent)
    (h : hst 0 = (s₀, []) ∧ ∃ Ie Ii : SInst, X.exp.mod.IsInst Ie ∧ X.imp.mod.IsInst Ii ∧
      HLinked2.SpecSessProd (profile o) X Ie Ii (HLinked2.logG g) a out hst) :
    hst 0 = (s₀, []) ∧ ∃ Ie Ii : SInst, eY.mod.IsInst Ie ∧ iY.mod.IsInst Ii ∧
      HLinked2.SpecSessProd (profile o) ⟨eY, iY, wY, X.host⟩ Ie Ii (HLinked2.logG g)
        (Linked2.castStream (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len a) out hst := by
  obtain ⟨h₀, Ie₀, Ii₀, hIe₀, hIi₀, u, π, hs, hu0, hπ0, hk⟩ := h
  have e1 : IeX = Ie₀ := NumModule.IsInst.unique hIe hIe₀
  have e2 : IiX = Ii₀ := ImpModule.IsInst.unique hIi hIi₀
  subst e1 e2
  refine ⟨h₀, IeY, IiY, hIe', hIi', ?_⟩
  have hTG := HLinkedSession.HostTyped.logG hT
  let Sub : ℕ → Type := fun k =>
    {p : X.St // Rel (u k, π k, p.2.2) p ∧ Refuses (HLinked2.logG g) p.2.2 (hst k)}
  have step : ∀ k (p : Sub k), ∃ (q : Sub (k + 1)) (H' : List (Call (sigN X.host.length))),
      HLinked2.SessSpec (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY p.1.1 p.1.2.1
        [(Fin.cast len (a k).1, (a k).2)] [out k] [H'] q.1.1 q.1.2.1 ∧
      HostRun (HLinked2.logG g) (hst k) H' (hst (k + 1)) := by
    intro k ⟨⟨u', π', R⟩, hRel, hRef⟩
    obtain ⟨R₁, u₁', π₁', H', hRel₁, hRef₁, hS', hr'⟩ :=
      round_back hTG hB len hty hRel hRef (ht k) (hk k).1 (hk k).2
    exact ⟨⟨(u₁', π₁', R₁), hRel₁, hRef₁⟩, H', hS', hr'⟩
  choose F H' hF using step
  let seq : (k : ℕ) → Sub k := fun k =>
    Nat.rec ⟨(IiY.store, IeY.store, []), by rw [hu0, hπ0]; exact h0,
      fun _ h => (List.not_mem_nil h).elim⟩ (fun k p => F k p) k
  exact ⟨fun k => (seq k).1.1, fun k => (seq k).1.2.1, fun k => H' k (seq k), rfl, rfl,
    fun k => hF k (seq k)⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
