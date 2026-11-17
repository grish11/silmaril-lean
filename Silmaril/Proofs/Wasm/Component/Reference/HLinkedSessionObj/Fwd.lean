module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Bisim2
public import Silmaril.Wasm.Component.Reference.HLinkedSessionInf.Thms
import Silmaril.Proofs.Wasm.Component.Reference.ImpIR
import Silmaril.Proofs.Wasm.Component.Reference.SpecToIR
import Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy.RefSess

/-!
# The reference equivalence gives equal session objects

From `HLinked2.RefSessEquivFull` at `profile o` (through `HLinked2.RefSessEquivFull.iff_spec` and
`HLinked2.sessObs_eq`), the finite, divergence and host-chatter observations at the instances
agree under every scripted host (`ObsSame`, `DivSame`, `InfSame`), so the session objects are
equal (`compSession_eq_of_full`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile Thread)
open Silmaril.Wasm.Component.Runtime (HostFuncId)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "RVal" => Silmaril.Wasm.Component.Value.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {l : HLinked2} {Ie Ii : SInst}

/-- The session object is the threading of the triple at the instances. -/
theorem compSession_eq {P : Profile} (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) :
    HLinked2.compSession P l =
      StratSession.threadS (HLinked2.compTripleS P l Ie Ii) (Ii.store, Ie.store, []) := by
  have h : ∃ Ie Ii : SInst, l.exp.mod.IsInst Ie ∧ l.imp.mod.IsInst Ii := ⟨Ie, Ii, hIe, hIi⟩
  rw [HLinked2.compSession, dite_eq_left_of_eq_true (eq_true h)]
  obtain rfl := NumModule.IsInst.unique h.choose_spec.choose_spec.1 hIe
  obtain rfl := ImpModule.IsInst.unique h.choose_spec.choose_spec.2 hIi
  rfl

theorem sObs_iff {P : Profile} (prof : ProfileKind) (hl : l.Adequate) (hIe : l.exp.mod.IsInst Ie)
    (hIi : l.imp.mod.IsInst Ii) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (hT : l.HostTyped g) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls l.imp calls)
    (p : List (Option (List IVal)) × (σ × List HLinked2.HostEvent)) :
    p ∈ SObs P l Ie Ii calls g s₀ ↔ (refOuts p.1, p.2) ∈ HLinked2.sessObs P prof l g s₀ calls := by
  rw [HLinked2.sessObs_eq P prof hl g hT s₀ calls ht]
  constructor
  · rintro ⟨hs, u, π, h, hr⟩
    exact ⟨Ie, Ii, p.1, hs, u, π, hIe, hIi, h, hr, rfl⟩
  · rintro ⟨Ie', Ii', outs, hs, u, π, hIe', hIi', h, hr, ho⟩
    obtain rfl := NumModule.IsInst.unique hIe' hIe
    obtain rfl := ImpModule.IsInst.unique hIi' hIi
    obtain rfl := SessionAdequacy.refOuts_inj ho
    exact ⟨hs, u, π, h, hr⟩

theorem dObs_eq {P : Profile} (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) : DObs P l Ie Ii calls j vs g s₀ = HLinked2.sessDivs P l g s₀ calls j vs := by
  ext p
  constructor
  · rintro ⟨hs, u, π, st, h, hr, hd⟩
    exact ⟨Ie, Ii, hs, u, π, st, hIe, hIi, h, hr, hd⟩
  · rintro ⟨Ie', Ii', hs, u, π, st, hIe', hIi', h, hr, hd⟩
    obtain rfl := NumModule.IsInst.unique hIe' hIe
    obtain rfl := ImpModule.IsInst.unique hIi' hIi
    exact ⟨hs, u, π, st, h, hr, hd⟩

theorem hObs_eq {P : Profile} (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) {σ : Type}
    (g : σ → HostFuncId → List RVal → Option (List RVal × σ)) (s₀ : σ)
    (calls : List (Fin l.imp.exports.length × List IVal)) (j : Fin l.imp.exports.length)
    (vs : List IVal) : HObs P l Ie Ii calls j vs g s₀ = HLinked2.sessHProds P l g s₀ calls j vs := by
  ext p
  constructor
  · rintro ⟨hs, u, π, hst, h, hr, hd, hlog⟩
    exact ⟨Ie, Ii, hs, u, π, hst, hIe, hIi, h, hr, hd, hlog⟩
  · rintro ⟨Ie', Ii', hs, u, π, hst, hIe', hIi', h, hr, hd, hlog⟩
    obtain rfl := NumModule.IsInst.unique hIe' hIe
    obtain rfl := ImpModule.IsInst.unique hIi' hIi
    exact ⟨hs, u, π, hst, h, hr, hd, hlog⟩

/-- **The reference equivalence gives equal session objects** (`profile o`). -/
theorem compSession_eq_of_full {o : GrowOracle} {prof : ProfileKind} {e' : Simple} {i' : SimpleI}
    {w' : List Nat} (hl : l.Adequate) (hl' : (⟨e', i', w', l.host⟩ : HLinked2).Adequate)
    (h : HLinked2.RefSessEquivFull (profile o) prof l ⟨e', i', w', l.host⟩) :
    HLinked2.compSession (profile o) l = HLinked2.compSession (profile o) ⟨e', i', w', l.host⟩ := by
  obtain ⟨hH, hdiv, -⟩ := (HLinked2.RefSessEquivFull.iff_spec hl hl').1 h
  have len := hH.len
  have hty : LinkedSessionEquiv.SameTyL l.toL2 ⟨e', i', w'⟩ len := hH.ty
  obtain ⟨Ie, hIe⟩ := hl.expInst.inst
  obtain ⟨Ii, hIi⟩ := hl.impInst.inst
  obtain ⟨Ie', hIe'⟩ := hl'.expInst.inst
  obtain ⟨Ii', hIi'⟩ := hl'.impInst.inst
  rw [compSession_eq hIe hIi, compSession_eq hIe' hIi']
  refine threadS_eq_of_same len hty ?_ ?_ ?_
  · intro calls ht S hS
    ext p
    rw [sObs_iff prof hl hIe hIi _ hS 0 calls ht,
      sObs_iff (l := ⟨e', i', w', l.host⟩) prof hl' hIe' hIi' _ hS 0 _
        (LinkedSessionEquiv.typedCalls_castL hty ht),
      hH.obs calls ht _ hS 0]
  · intro calls ht j vs hvs S hS
    rw [dObs_eq hIe hIi, dObs_eq (l := ⟨e', i', w', l.host⟩) hIe' hIi']
    exact (hdiv calls j vs ht hvs _ hS 0).1
  · intro calls ht j vs hvs S hS
    rw [hObs_eq hIe hIi, hObs_eq (l := ⟨e', i', w', l.host⟩) hIe' hIi']
    exact (hdiv calls j vs ht hvs _ hS 0).2

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj
