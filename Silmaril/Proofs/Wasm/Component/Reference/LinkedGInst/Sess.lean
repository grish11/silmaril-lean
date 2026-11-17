module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst.Inst
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv.Sess
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Simple
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedG.Main
public import Silmaril.Wasm.Component.Reference.LinkedG.Thms

/-!
# Sessions of a linked component with an abstract exporter, read back from instantiation

* `sess_refToSpecU`: every session behaviour of typed calls of `lg.toRef` is the reference image
  of a `LinkedG.SessSpec` session from the importer's instance store and the exporter's initial
  state: the instantiation result is unique (`instBehavioursG_toRef`), ends between calls
  (`readyB_init`, `statB_init`) with no waiting thread (`afterG_waiting`), and `sessL_invB` of
  `LinkedGInv` reads the session back;
* `sessObs_eqU`: with `sess_specToRefB` of `LinkedGInit`, the session observations are exactly
  those images;
* `sessAdequacy_fullU`: with `LinkedG.sessIR_iff` (#839), exactly the images of the outcome lists
  whose session play is a play of `lg.toComp.den (impSem P)`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInv
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {lg : LinkedG}

/-- **Reference sessions of a linked component with an abstract exporter are specification
sessions**, for an exporter meeting R1, R3 as `BwdF`, R4 as `InitU`, R5 and R6. -/
theorem sess_refToSpecU (P : Profile) (prof : ProfileKind) {d : lg.exp.RefData P}
    (hInit : d.InitU) (hFr : d.Frame) (hBw : d.BwdF) (hRes : d.Resume) (hB : d.Bounded)
    (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) {calls : List (Fin lg.imp.exports.length × List IVal)}
    (ht : SimpleI.TypedCalls lg.imp calls) {Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hI : lg.imp.mod.IsInst Ii) {o : List (Option (List Silmaril.Wasm.Component.Reference.Val))}
    (ho : o ∈ LinkedG.sessObs prof lg impl h₀ calls) :
    ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : lg.exp.St),
      LinkedG.SessSpec P lg Ii Ii.store lg.exp.init calls outs u' s' ∧ o = refOuts outs := by
  obtain ⟨m₁, pl, F, es, r, hA, hrs, hh, hall⟩ :=
    instBehavioursG_toRef hInit hFr hW hIg hIi hIa ⟨hS.data, hS.elems⟩ hNI hI prof impl h₀
  obtain ⟨m₀, inst, es', fs, hr, hfs, hSq⟩ := ho
  rw [hall] at hr
  obtain ⟨rfl, rfl, rfl⟩ := InstResult.instance.inj (Set.mem_singleton_iff.1 hr)
  have hfs' : fs = calls.map fun q => (⟨m₁.store.funcs.length + q.1⟩ : FuncId) :=
    Option.some.inj (hfs.symm.trans (mapM_lookupG hIg _ calls))
  subst hfs'
  rw [zip_callArgsG] at hSq
  have ST := statB_init hW hn hIg hIa hff hI hA.toInitAt hh
  have R := readyB_init hFr hB hW hn hI hS hA.toInitAt rfl rfl rfl hrs hh
  exact sessL_invB ST hFr hBw hRes hB calls _ _ _ 0 o R (afterG_waiting hA) ht hSq

/-- **The session observations of a linked component with an abstract exporter are the
specification sessions'.** -/
theorem sessObs_eqU (P : Profile) (prof : ProfileKind) (he : lg.exp.RefAdeqU P)
    (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) (calls : List (Fin lg.imp.exports.length × List IVal))
    (ht : SimpleI.TypedCalls lg.imp calls) {Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hI : lg.imp.mod.IsInst Ii) :
    LinkedG.sessObs prof lg impl h₀ calls =
      {o | ∃ (outs : List (Option (List IVal))) (u' : Store Nat) (s' : lg.exp.St),
        LinkedG.SessSpec P lg Ii Ii.store lg.exp.init calls outs u' s' ∧ o = refOuts outs} := by
  obtain ⟨d, hFr, hFw, hBw, hInit, hRes, hB⟩ := he
  ext o
  constructor
  · exact sess_refToSpecU P prof hInit hFr hBw hRes hB hW hn hIg hIi hIa hff hS hNI impl h₀ ht hI
  · rintro ⟨outs, u', s', hspec, rfl⟩
    exact sess_specToRefB P prof (initU_initS hInit) hFr hFw hRes hB hW hn hIg hIi hIa hff hS hNI
      impl h₀ hI hspec

/-- **Finite session adequacy of a linked component with an abstract exporter**: the session
observations of typed calls are the reference images of the outcome lists whose session play is
a play of `lg.toComp.den (impSem P)`. -/
theorem sessAdequacy_fullU (P : Profile) (prof : ProfileKind) (he : lg.exp.RefAdeqU P)
    (hA : lg.exp.Adeq P) (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good)
    (hIi : lg.imp.Inst) (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree)
    (hS : Linked2.ModSplitOk lg.imp.mod.mod) (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n)
    {σ : Type} (impl : HostImpl (core3P P) σ) (h₀ : σ)
    (calls : List (Fin lg.imp.exports.length × List IVal)) (ht : SimpleI.TypedCalls lg.imp calls) :
    LinkedG.sessObs prof lg impl h₀ calls =
      {o | ∃ outs, o = refOuts outs ∧ calls.length = outs.length ∧
        lg.sessMoves calls outs ∈ lg.toComp.den (impSem P)} := by
  obtain ⟨Ii, hI⟩ := hIi.inst
  rw [sessObs_eqU P prof he hW hn hIg hIi hIa hff hS hNI impl h₀ calls ht hI]
  ext o
  constructor
  · rintro ⟨outs, u', s', hspec, rfl⟩
    exact ⟨outs, rfl, LinkedG.sessSpec_lengthG hspec,
      Silmaril.Wasm.Component.Reference.LinkedG.sess_specToIR hA hIg hI hspec⟩
  · rintro ⟨outs, rfl, hlen, hm⟩
    obtain ⟨u', s', hspec⟩ :=
      Silmaril.Wasm.Component.Reference.LinkedG.irToSpec hA hIg hI hW calls outs ht hlen hm
    exact ⟨outs, u', s', hspec, rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst
