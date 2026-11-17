module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Ready

/-!
# Sessions of a linked component with an abstract exporter, from instantiation

`sess_specToRefB`: every `LinkedG.SessSpec` session from the instances' initial states (the
importer's instance store and the exporter's `e.init`) is a session behaviour of `lg.toRef`
(`LinkedG.sessObs`): the instantiation (`instG_run`) ends between calls (`readyB_init`, with
the static facts `statB_init`), from where `sessL_fwdB` of `LinkedGRound` runs the session.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

variable {lg : LinkedG}

theorem exportMapG_lookup (hIg : lg.imp.Good) (fb : Nat) (j : Fin lg.imp.exports.length) :
    (exportMapG lg fb).lookup lg.imp.exports[j].name = some ⟨fb + j⟩ :=
  lookup_mapIdx_val (·.name) (fun i => (⟨i⟩ : FuncId)) fb lg.imp.exports j j.isLt hIg.names

theorem mapM_lookupG (hIg : lg.imp.Good) (fb : Nat) :
    ∀ (calls : List (Fin lg.imp.exports.length × List IVal)),
      (calls.map fun q => (lg.imp.exports[q.1].name, q.2.map toRefVal)).mapM
          (fun q => (exportMapG lg fb).lookup q.1) =
        some (calls.map fun q => (⟨fb + q.1⟩ : FuncId))
  | [] => rfl
  | q :: calls => by
    simp only [List.map_cons, List.mapM_cons, exportMapG_lookup hIg fb q.1,
      mapM_lookupG hIg fb calls]
    rfl

theorem zip_callArgsG (fb : Nat) (calls : List (Fin lg.imp.exports.length × List IVal)) :
    (calls.map fun q => (⟨fb + q.1⟩ : FuncId)).zip
        ((calls.map fun q => (lg.imp.exports[q.1].name, q.2.map toRefVal)).map Prod.snd) =
      callArgsG lg (fun j => fb + j) calls := by
  induction calls with
  | nil => rfl
  | cons q calls ih =>
    simp only [List.map_cons, List.zip_cons_cons, ih]
    rfl

/-- **Specification sessions of a linked component with an abstract exporter are reference
sessions**: for an exporter meeting R1, R2, R4 with what the parent reads (`InitS`), R5 and R6,
and an importer as in `Linked2` (in the instantiation and split fragments, within the flat
arities, float-free, export names not generated type names, an injective well-typed wiring), the
reference images of the outcomes of every `LinkedG.SessSpec` session from the importer's instance
store and the exporter's initial state are session behaviours of `lg.toRef`. -/
theorem sess_specToRefB (P : Profile) (prof : ProfileKind) {d : lg.exp.RefData P}
    (hInit : d.InitS) (hFr : d.Frame) (hFw : d.Fwd) (hRes : d.Resume) (hB : d.Bounded)
    (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good) (hIi : lg.imp.Inst)
    (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hNI : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n) {σ : Type}
    (impl : HostImpl (core3P P) σ) (h₀ : σ) {calls : List (Fin lg.imp.exports.length × List IVal)}
    {Ii : Silmaril.Wasm.Game.ScalarInstance} (hI : lg.imp.mod.IsInst Ii)
    {outs : List (Option (List IVal))} {u' : Store Nat} {s' : lg.exp.St}
    (hspec : LinkedG.SessSpec P lg Ii Ii.store lg.exp.init calls outs u' s') :
    refOuts outs ∈ LinkedG.sessObs prof lg impl h₀ calls := by
  obtain ⟨tr, m₁, pl, F, es, r, hA, hrs, hh, hs, hnh, ho⟩ :=
    instG_run (prof := prof) (impl := impl) hInit hFr hW hIg hIi hIa ⟨hS.data, hS.elems⟩ hNI hI h₀
  have ST := statB_init hW hn hIg hIa hff hI hA hh
  have R := readyB_init hFr hB hW hn hI hS hA rfl rfl rfl hrs hh
  have hSq := sessL_fwdB (prof := prof) (impl := impl) ST hFr hFw hRes hB hspec _ 0 R
  refine ⟨afterG lg Ii m₁ r, ⟨0⟩, exportMapG lg m₁.store.funcs.length,
    calls.map fun q => (⟨m₁.store.funcs.length + q.1⟩ : FuncId), ?_, mapM_lookupG hIg _ calls, ?_⟩
  · refine ⟨tr, hs, hnh, rfl, R.lock, ?_⟩
    rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]
  · rw [zip_callArgsG]
    exact hSq

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
