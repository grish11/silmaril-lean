module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.InfT3

/-!
# The bisimulation of two linked components with the same observations under scripted hosts

`Inv` is a bisimulation between the host-realizable triples (`isBisim`), so their session objects
from the instances' stores are equal (`threadS_eq_of_same`). The other direction of each transfer
is the transfer for the swapped pair (`inv_swap`, `obsSame_swap`, `divSame_swap`, `infSame_swap`).
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

theorem castCalls_back (len : X.imp.exports.length = iY.exports.length)
    (calls : List (Fin X.imp.exports.length × List IVal)) :
    Linked2.castCalls (l := ⟨eY, iY, wY⟩) (l' := X.toL2) len.symm
      (Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len calls) = calls :=
  LinkedSessionEquiv.castCalls_castL (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len calls

theorem castCalls_fwd (len : X.imp.exports.length = iY.exports.length)
    (calls : List (Fin iY.exports.length × List IVal)) :
    Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len
      (Linked2.castCalls (l := ⟨eY, iY, wY⟩) (l' := X.toL2) len.symm calls) = calls :=
  LinkedSessionEquiv.castCalls_castL (l := ⟨eY, iY, wY⟩) (l' := X.toL2) len.symm calls

theorem inv_swap {len : X.imp.exports.length = iY.exports.length}
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len) {sX sY : X.St}
    (h : Inv X IeX IiX eY iY wY IeY IiY len o sX sY) :
    Inv ⟨eY, iY, wY, X.host⟩ IeY IiY X.exp X.imp X.wire IeX IiX len.symm o sY sX := by
  obtain ⟨hR, callsX, outs, hsX, hsY, ht, hX, hY, hRX, hRY, hvX, hvY, hans⟩ := h
  refine ⟨hR.symm, Linked2.castCalls (l := X.toL2) (l' := ⟨eY, iY, wY⟩) len callsX, outs, hsY,
    hsX, LinkedSessionEquiv.typedCalls_castL hty ht, hY, ?_, hR ▸ hRY, hR ▸ hRX, hvY, hvX,
    hans.symm⟩
  rw [castCalls_back]
  exact hX

theorem obsSame_swap {len : X.imp.exports.length = iY.exports.length}
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (h : ObsSame X IeX IiX eY iY wY IeY IiY len o) :
    ObsSame ⟨eY, iY, wY, X.host⟩ IeY IiY X.exp X.imp X.wire IeX IiX len.symm o := by
  intro callsY ht S hS
  have := h _ (LinkedSessionEquiv.typedCalls_castL (LinkedSessionEquiv.sameTy_symmL hty) ht) S hS
  rw [castCalls_fwd] at this
  exact this.symm

theorem divSame_swap {len : X.imp.exports.length = iY.exports.length}
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (h : DivSame X IeX IiX eY iY wY IeY IiY len o) :
    DivSame ⟨eY, iY, wY, X.host⟩ IeY IiY X.exp X.imp X.wire IeX IiX len.symm o := by
  intro callsY ht j vs hvs S hS
  have hvs' : ValTy.checkList X.imp.exports[Fin.cast len.symm j].ty.params vs = true := by
    have := hty (Fin.cast len.symm j)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at this
    rw [← this]; exact hvs
  have := h _ (LinkedSessionEquiv.typedCalls_castL (LinkedSessionEquiv.sameTy_symmL hty) ht)
    (Fin.cast len.symm j) vs hvs' S hS
  rw [castCalls_fwd] at this
  simp only [Fin.cast_cast, Fin.cast_eq_self] at this
  exact this.symm

theorem infSame_swap {len : X.imp.exports.length = iY.exports.length}
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (h : InfSame X IeX IiX eY iY wY IeY IiY len o) :
    InfSame ⟨eY, iY, wY, X.host⟩ IeY IiY X.exp X.imp X.wire IeX IiX len.symm o := by
  intro callsY ht j vs hvs S hS
  have hvs' : ValTy.checkList X.imp.exports[Fin.cast len.symm j].ty.params vs = true := by
    have := hty (Fin.cast len.symm j)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at this
    rw [← this]; exact hvs
  have := h _ (LinkedSessionEquiv.typedCalls_castL (LinkedSessionEquiv.sameTy_symmL hty) ht)
    (Fin.cast len.symm j) vs hvs' S hS
  rw [castCalls_fwd] at this
  simp only [Fin.cast_cast, Fin.cast_eq_self] at this
  exact this.symm

variable {l : HLinked2} {Ie Ii : SInst}

theorem compFin_no_trap {P : Profile} {s : l.St} {a : Nat × Payload}
    {c : List (Call (sigN l.host.length))} : (c, End.trap) ∉ HLinked2.compFin P l Ie Ii s a := by
  intro hm
  simp only [HLinked2.compFin] at hm
  split at hm
  · simp at hm
  · rcases hm with ⟨_, _, _, _, _, _, he⟩ | ⟨_, _, _, _, _, _, _, he⟩ | ⟨_, _, _, he⟩ <;> cases he

/-- The pending calls of the base triple transfer along `Inv`. -/
theorem satP_transfer (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (hobs : ObsSame X IeX IiX eY iY wY IeY IiY len o)
    (hdobs : DivSame X IeX IiX eY iY wY IeY IiY len o)
    (hiobs : InfSame X IeX IiX eY iY wY IeY IiY len o) {sX sY : X.St}
    (hI : Inv X IeX IiX eY iY wY IeY IiY len o sX sY) {a : Nat × Payload}
    {x : List (Call (sigN X.host.length)) × (sigN X.host.length).Op}
    (hx : x ∈ satP (HLinked2.compFin (profile o) X IeX IiX, fun _ _ => ∅,
      HLinked2.compInf (profile o) X IeX IiX) sX a) :
    x ∈ satP (HLinked2.compFin (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY, fun _ _ => ∅,
      HLinked2.compInf (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY) sY a := by
  rcases hx with hx | ⟨_, _, hd, _⟩ | ⟨d, e, hd, hp⟩ | ⟨ω, hω, k, hk⟩
  · exact hx.elim
  · exact hd.elim
  · rcases e with ⟨b, s₁⟩ | _ | _
    · obtain ⟨sY₁, h, -⟩ := ret_transfer len hty hobs hI hd
      exact .inr (.inr (.inl ⟨d, _, h, hp⟩))
    · exact (compFin_no_trap hd).elim
    · exact .inr (.inr (.inl ⟨d, _, div_transfer len hty hdobs hI hd, hp⟩))
  · exact .inr (.inr (.inr ⟨ω, inf_transfer len hty hiobs hI hω, k, hk⟩))

theorem satP_compTripleS {P : Profile} {s : l.St} {a : Nat × Payload}
    {x : List (Call (HLinked2.hostSig l.host)) × (HLinked2.hostSig l.host).Op} :
    x ∈ satP (HLinked2.compTripleS P l Ie Ii) s a ↔
      (x.1.map StratLegal.liftCall, x.2) ∈
        satP (HLinked2.compFin P l Ie Ii, fun _ _ => ∅, HLinked2.compInf P l Ie Ii) s a :=
  StratLegal.mem_satP_restrict admissible_sat

/-- **`Inv` is a bisimulation.** -/
theorem isBisim (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (hobs : ObsSame X IeX IiX eY iY wY IeY IiY len o)
    (hdobs : DivSame X IeX IiX eY iY wY IeY IiY len o)
    (hiobs : InfSame X IeX IiX eY iY wY IeY IiY len o) :
    IsBisim (HLinked2.compTripleS (profile o) X IeX IiX)
      (HLinked2.compTripleS (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY)
      (Inv X IeX IiX eY iY wY IeY IiY len o) := by
  have hty' := LinkedSessionEquiv.sameTy_symmL hty
  have hobs' := obsSame_swap hty hobs
  have hdobs' := divSame_swap hty hdobs
  have hiobs' := infSame_swap hty hiobs
  intro sX sY hI
  have hI' := inv_swap hty hI
  refine ⟨fun a c => ⟨fun h => (compFin_no_trap h).elim, fun h => (compFin_no_trap h).elim⟩,
    fun a c => ⟨fun h => div_transfer len hty hdobs hI h,
      fun h => div_transfer len.symm hty' hdobs' hI' h⟩, ?_, ?_, ?_, ?_⟩
  · funext a
    ext x
    rw [satP_compTripleS, satP_compTripleS]
    exact ⟨satP_transfer len hty hobs hdobs hiobs hI, satP_transfer len.symm hty' hobs' hdobs'
      hiobs' hI'⟩
  · funext a
    ext ω
    exact ⟨fun h => inf_transfer len hty hiobs hI h, fun h => inf_transfer len.symm hty' hiobs' hI' h⟩
  · intro a c b s₁ h
    obtain ⟨sY₁, h', hI₁⟩ := ret_transfer len hty hobs hI h
    exact ⟨sY₁, h', hI₁⟩
  · intro a c b sY₁ h
    obtain ⟨sX₁, h', hI₁⟩ := ret_transfer len.symm hty' hobs' hI' h
    exact ⟨sX₁, h', inv_swap hty' hI₁⟩

/-- **Equal session objects from the same observations under scripted hosts.** -/
theorem threadS_eq_of_same (len : X.imp.exports.length = iY.exports.length)
    (hty : LinkedSessionEquiv.SameTyL X.toL2 ⟨eY, iY, wY⟩ len)
    (hobs : ObsSame X IeX IiX eY iY wY IeY IiY len o)
    (hdobs : DivSame X IeX IiX eY iY wY IeY IiY len o)
    (hiobs : InfSame X IeX IiX eY iY wY IeY IiY len o) :
    StratSession.threadS (HLinked2.compTripleS (profile o) X IeX IiX) (IiX.store, IeX.store, []) =
      StratSession.threadS (HLinked2.compTripleS (profile o) ⟨eY, iY, wY, X.host⟩ IeY IiY)
        (IiY.store, IeY.store, []) := by
  have h0 : Inv X IeX IiX eY iY wY IeY IiY len o (IiX.store, IeX.store, [])
      (IiY.store, IeY.store, []) :=
    by
      refine ⟨rfl, [], [], [], [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · intro q hq; simp at hq
      · exact .nil _ _
      · exact .nil _ _
      · exact .nil _
      · exact .nil _
      · intro x hx; simp at hx
      · intro x hx; simp at hx
  exact StratSession.threadS_eq_of_obsEq ⟨_, isBisim len hty hobs hdobs hiobs, h0⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
