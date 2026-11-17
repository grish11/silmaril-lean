module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.BackProd

/-!
# Equal session objects give the reference equivalence; the injection

Equal host-realizable session objects of store-deterministic triples without plain traps are
bisimilar initial states (`StratSession.threadS_eq_iff`); along the bisimulation and its flip the
finite observations, divergences, host chatter and infinite sessions transfer under every typed
host, which is `HLinked2.RefSessEquivFull` through `HLinked2.RefSessEquivFull.iff_spec`
(`refSessEquivFull_of_compSession`). With `compSession_heq_of_full` this is the injection
(`compSession_inj_full`).
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

variable {l : HLinked2} {o : GrowOracle} {prof : ProfileKind}

theorem castStream_back {e' : Simple} {i' : SimpleI} {w' : List Nat}
    (len : l.imp.exports.length = i'.exports.length) (a : ℕ → Fin l.imp.exports.length × List IVal) :
    Linked2.castStream (l := ⟨e', i', w'⟩) (l' := l.toL2) len.symm
      (Linked2.castStream (l := l.toL2) (l' := ⟨e', i', w'⟩) len a) = a := by
  funext k
  simp [Linked2.castStream]

/-- **Equal session objects give the reference equivalence** (`profile o`). -/
theorem refSessEquivFull_of_compSession {l' : HLinked2} (hl : l.Adequate) (hl' : l'.Adequate)
    (hS : HLinked2.SameTypes l l')
    (hE : HEq (HLinked2.compSession (profile o) l) (HLinked2.compSession (profile o) l')) :
    HLinked2.RefSessEquivFull (profile o) prof l l' := by
  obtain ⟨e', i', w', h'⟩ := l'
  have hh : h' = l.host := hS.host
  subst hh
  have hE' := eq_of_heq hE
  have len := hS.len
  have hty : LinkedSessionEquiv.SameTyL l.toL2 ⟨e', i', w'⟩ len := hS.ty
  have hty' := LinkedSessionEquiv.sameTy_symmL hty
  obtain ⟨Ie, hIe⟩ := hl.expInst.inst
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  obtain ⟨Ie', hIe'⟩ := hl'.expInst.inst
  obtain ⟨Ii', hIi'⟩ := hl'.impInst.inst
  rw [compSession_eq hIe hIi, compSession_eq hIe' hIi'] at hE'
  obtain ⟨Rel, hB, h0⟩ := (StratSession.threadS_eq_iff
    (storeDet_compTripleS (l := l) (Ie := Ie) (Ii := Ii) (o := o))
    (storeDet_compTripleS (l := ⟨e', i', w', l.host⟩) (Ie := Ie') (Ii := Ii') (o := o))
    (noPlainTrap_compTripleS (l := l) (Ie := Ie) (Ii := Ii))
    (noPlainTrap_compTripleS (l := ⟨e', i', w', l.host⟩) (Ie := Ie') (Ii := Ii'))).1 hE'
  have hB' := hB.flip
  refine (HLinked2.RefSessEquivFull.iff_spec hl hl').2 ⟨⟨len, hS.ty, rfl, ?_⟩, ?_, ?_⟩
  · intro calls ht σ g hT s₀
    refine Set.Subset.antisymm (sessObs_sub prof hl hl' hIe hIi hIe' hIi' hB h0 len hty calls ht g
      hT s₀) ?_
    have := sessObs_sub (X := ⟨e', i', w', l.host⟩) (eY := l.exp) (iY := l.imp) (wY := l.wire)
      prof hl' hl hIe' hIi' hIe hIi hB' h0 len.symm hty' _
      (LinkedSessionEquiv.typedCalls_castL hty ht) g hT s₀
    rwa [castCalls_back] at this
  · intro calls j vs ht hvs σ g hT s₀
    have ht' := LinkedSessionEquiv.typedCalls_castL hty ht
    have hvs' : ValTy.checkList i'.exports[Fin.cast len j].ty.params vs = true := by
      rw [hty j]; exact hvs
    refine ⟨Set.Subset.antisymm (sessDivs_sub hIe hIi hIe' hIi' hB h0 len hty calls ht j vs hvs g
      hT s₀) ?_, Set.Subset.antisymm (sessHProds_sub hIe hIi hIe' hIi' hB h0 len hty calls ht j vs
      hvs g hT s₀) ?_⟩
    · have := sessDivs_sub (X := ⟨e', i', w', l.host⟩) (eY := l.exp) (iY := l.imp) (wY := l.wire)
        hIe' hIi' hIe hIi hB' h0 len.symm hty' _ ht' _ vs hvs' g hT s₀
      rw [castCalls_back] at this
      simpa using this
    · have := sessHProds_sub (X := ⟨e', i', w', l.host⟩) (eY := l.exp) (iY := l.imp) (wY := l.wire)
        hIe' hIi' hIe hIi hB' h0 len.symm hty' _ ht' _ vs hvs' g hT s₀
      rw [castCalls_back] at this
      simpa using this
  · intro a out ht σ g hT s₀ hst
    have ht' : ∀ k, ValTy.checkList i'.exports[(Linked2.castStream (l := l.toL2)
        (l' := ⟨e', i', w'⟩) len a k).1].ty.params (a k).2 = true := by
      intro k
      show ValTy.checkList i'.exports[Fin.cast len (a k).1].ty.params (a k).2 = true
      rw [hty (a k).1]; exact ht k
    refine ⟨specSessProd_sub hIe hIi hIe' hIi' hB h0 len hty a out ht g hT s₀ hst, fun h => ?_⟩
    have := specSessProd_sub (X := ⟨e', i', w', l.host⟩) (eY := l.exp) (iY := l.imp) (wY := l.wire)
      hIe' hIi' hIe hIi hB' h0 len.symm hty' _ out ht' g hT s₀ hst h
    rwa [castStream_back] at this

/-- **The injection** (`profile o`). -/
theorem compSession_inj_full {l' : HLinked2} (hl : l.Adequate) (hl' : l'.Adequate) :
    HLinked2.RefSessEquivFull (profile o) prof l l' ↔
      HLinked2.SameTypes l l' ∧
        HEq (HLinked2.compSession (profile o) l) (HLinked2.compSession (profile o) l') :=
  ⟨compSession_heq_of_full hl hl', fun ⟨hS, hE⟩ => refSessEquivFull_of_compSession hl hl' hS hE⟩

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
