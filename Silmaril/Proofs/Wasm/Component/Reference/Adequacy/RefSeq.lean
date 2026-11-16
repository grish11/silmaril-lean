module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.RefRun
public import Silmaril.Wasm.Component.Reference.Adequacy.Defs

/-!
# Specification sequences are reference behaviours

`seq_specToRef`: the converse of `seq_refToSpec`. A chain of returned calls of the specification
from the instance's store (`SeqSpec`), followed by a terminating outcome of the last call at the
store reached, is a behaviour of instantiating `c.toRef` and calling its exports
(`seqBehaviours`), at every profile and component choice profile. The single-call case is
`specToRef`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)
open Silmaril.Wasm.Execution.Core (Store)

variable {P : Profile} {prof : ProfileKind}

/-- **Instantiation reaches the instance.** -/
theorem inst_forward (P : Profile) (prof : ProfileKind) {c : Simple} (hc : c.Good)
    (hi : c.Inst) :
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (cs : (core3P P).Store (CanonHost (core3P P))),
      c.mod.IsInst I ∧ Store.mapH (fun _ => (0 : Nat)) cs = I.store ∧
      InstResult.instance (afterInst P cs (liftedFuncs P (fun k => I.addrs.getD k 0) c)) ⟨0⟩
        (exportMap c) ∈ instBehaviours prof (refHost P) (initConfig ()) c.toRef [] := by
  obtain ⟨I, cs, ci, hF⟩ := coreFacts (Pf := P) hc hi
  obtain ⟨tr, hq, ho, d⟩ := inst_detRunL (prof := prof) (hr := (refHost P).hr)
    (D := (refHost P).dispatch) hF
  refine ⟨I, cs, hF.isInst, hF.store, tr, .cons (Step.hostRun ⟨rfl, rfl, rfl⟩) d.toDetRun.steps,
    ?_, rfl, rfl, ?_⟩
  · intro ev hm
    rcases hq _ hm with e | ⟨o, e⟩ <;> cases e
  · rw [ho, List.findSome?_cons, decodeInstantiated?_instantiatedObs]

variable {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}

/-- **Returned calls of the specification are resolved calls of the machine**, between calls. -/
theorem seqCalls_forward (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I) :
    ∀ (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
      (wss : List (List Silmaril.Wasm.Component.Val))
      (cs : (core3P P).Store (CanonHost (core3P P))) (ι : InstState) (G : Garb P) (k : Nat)
      (s' : Store Nat), ReadyAt I cs ι G k → TypedCalls c calls →
      SeqSpec P c I (Store.mapH (fun _ => 0) cs) (specCalls c calls) wss s' →
      ∃ cs' ι' G', SeqCalls prof (refHost P)
          (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) k (callArgs c calls)
          (wss.map (·.map toRefVal))
          (readyCfg cs' ι' (liftedFuncs P (fun k => I.addrs.getD k 0) c) G') ∧
        ReadyAt I cs' ι' G' (k + calls.length) ∧ Store.mapH (fun _ => (0 : Nat)) cs' = s'
  | [], wss, cs, ι, G, k, s', R, _, h => by
    cases h
    exact ⟨cs, ι, G, .nil _ _, R, rfl⟩
  | (j, vs) :: calls, wss, cs, ι, G, k, s', R, ht, h => by
    have h' : SeqSpec P c I (Store.mapH (fun _ => 0) cs)
        ((c.exports[j], vs) :: specCalls c calls) wss s' := h
    cases h' with
    | @cons _ s₁ _ _ _ ws _ wss' hret hseq =>
      have hvs : ValTy.checkList c.exports[j].ty.params vs = true := ht _ List.mem_cons_self
      have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
      have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs⟩
      obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
      obtain ⟨hff, hffr⟩ := hf _ hx
      have CR := callRun (prof := prof) C R hff hmax hres hmaxr hffr
        (liftedFuncs_get? (P := P) c (fun k => I.addrs.getD k 0) j.isLt)
      obtain ⟨cs₁, hcs₁, hcall⟩ := call_forward_ret C R CR hret
      have R₁ : ReadyAt I cs₁ (InstState.removeThread 1 (enterInst ι ⟨G.threads.length⟩))
          (nextGarb G c.exports[j] k j (I.addrs.getD c.exports[j].core 0) (vs.map toRefVal)
            (ws.map toRefVal)) (k + 1) :=
        ⟨hcs₁ ▸ hret.wellFormed hI (hc.core _ hx) R.wf, threadsOk_after _ _,
          fresh_next R.fresh _ _ _ _ _⟩
      obtain ⟨cs', ι', G', hS, R', hcs'⟩ := seqCalls_forward hc hf ha hI calls wss' cs₁ _ _
        (k + 1) s' R₁ (fun q hq => ht q (List.mem_cons_of_mem _ hq)) (hcs₁ ▸ hseq)
      have hk : k + 1 + calls.length = k + ((j, vs) :: calls).length := by
        simp only [List.length_cons]
        omega
      exact ⟨cs', ι', G', .cons hcall hS, hk ▸ R', hcs'⟩

/-- **A terminating outcome of the specification of the last call is a call behaviour.** -/
theorem last_forward (hc : c.Good) (hf : c.FloatFree) (ha : c.Arity) (hI : c.mod.IsInst I)
    {cs : (core3P P).Store (CanonHost (core3P P))} {ι : InstState} {G : Garb P} {n : Nat}
    (R : ReadyAt I cs ι G n) (j : Fin c.exports.length) {vs : List Silmaril.Wasm.Component.Val}
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ specAt P c I c.exports[j] vs (Store.mapH (fun _ => 0) cs)) (hterm : b.Term) :
    b ∈ callBehaviours prof (refHost P)
      (readyCfg cs ι (liftedFuncs P (fun k => I.addrs.getD k 0) c) G) ⟨n⟩ ⟨j⟩
      (vs.map toRefVal) := by
  have hx : c.exports[j] ∈ c.exports := List.getElem_mem j.isLt
  have C : CallCtxAt P c I cs c.exports[j] vs := ⟨hI, R.wf, hc.core _ hx, hvs⟩
  obtain ⟨hmax, hmaxr, hres⟩ := ha _ hx
  obtain ⟨hff, hffr⟩ := hf _ hx
  have CR := callRun (prof := prof) C R hff hmax hres hmaxr hffr
    (liftedFuncs_get? (P := P) c (fun k => I.addrs.getD k 0) j.isLt)
  unfold specAt at hb
  rw [C.lowerOk] at hb
  rcases hb with ⟨r, hr, rfl⟩ | ⟨rfl, -⟩
  · obtain ⟨m', out, hcalls, hout⟩ := call_forward_out C R CR hr
    exact .inl ⟨m', out, hcalls, hout.symm⟩
  · exact hterm.elim

/-- **Specification sequences are reference behaviours** (every profile and component choice
profile). -/
theorem seq_specToRef (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : c.mod.IsInst I) (calls : List (Fin c.exports.length × List Silmaril.Wasm.Component.Val))
    (wss : List (List Silmaril.Wasm.Component.Val)) (s : Store Nat) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls c calls)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (hseq : SeqSpec P c I I.store (specCalls c calls) wss s) {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ specAt P c I c.exports[j] vs s) (hterm : b.Term) :
    (wss.map (·.map toRefVal), b) ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal) := by
  obtain ⟨I', cs, hI', hcs, hinst⟩ := inst_forward P prof hc hi
  obtain rfl := NumModule.IsInst.unique hI' hI
  obtain ⟨cs', ι', G', hS, R', hcs'⟩ := seqCalls_forward (prof := prof) hc hf ha hI' calls wss cs
    {} ⟨[], [], [], [], [], [], []⟩ 0 s (ready_afterInst hI' hcs) ht (hcs ▸ hseq)
  have hlast := last_forward (prof := prof) hc hf ha hI' R' j hvs (hcs' ▸ hb) hterm
  refine .inl ⟨afterInst P cs (liftedFuncs P (fun k => I'.addrs.getD k 0) c), ⟨0⟩, exportMap c,
    calls.map fun q => (⟨q.1⟩ : FuncId),
    readyCfg cs' ι' (liftedFuncs P (fun k => I'.addrs.getD k 0) c) G', ⟨j⟩, hinst,
    mapM_lookup hc calls, ?_, exportMap_lookup hc j j.isLt, ?_⟩
  · rw [zip_callArgs]
    exact hS
  · rw [List.length_map, ← Nat.zero_add calls.length]
    exact hlast

/-- At the instance's store, terminating `exportSpec` outcomes are `specAt` outcomes. -/
theorem specAt_of_exportSpec (hI : c.mod.IsInst I) {x : SimpleExport}
    {vs : List Silmaril.Wasm.Component.Val} {b : Silmaril.Wasm.Component.Reference.Outcome}
    (hb : b ∈ exportSpec P c x vs) (hterm : b.Term) : b ∈ specAt P c I x vs I.store := by
  unfold exportSpec at hb
  unfold specAt
  cases hl : checkLower x.ty.params vs with
  | none => rw [hl] at hb; exact hb
  | some xs =>
    rw [hl] at hb
    rcases hb with ⟨r, ⟨I', hI', hr⟩, rfl⟩ | ⟨rfl, -⟩
    · obtain rfl := NumModule.IsInst.unique hI' hI
      exact .inl ⟨r, hr, rfl⟩
    · exact hterm.elim

/-- **Specification outcomes of one call are reference behaviours.** -/
theorem specToRef (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : c.FloatFree) (hi : c.Inst) (ha : c.Arity) (j : Fin c.exports.length)
    (vs : List Silmaril.Wasm.Component.Val) (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    {b : Silmaril.Wasm.Component.Reference.Outcome} (hb : b ∈ exportSpec P c c.exports[j] vs)
    (hterm : b.Term) :
    b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name (vs.map toRefVal) := by
  obtain ⟨I, hI⟩ := hi.inst
  have h := seq_specToRef P prof c hc hf hi ha hI [] [] I.store j vs (fun _ h => nomatch h)
    hvs (.nil _) (specAt_of_exportSpec hI hb hterm) hterm
  rcases h with ⟨m₀, inst, es, fs, mₙ, f, hr, -, hS, hl, hb₀⟩ | ⟨he, hr⟩ | ⟨he, hr⟩
  · simp only [List.map_nil, List.zip_nil_right] at hS
    cases hS
    exact .inl ⟨m₀, inst, es, f, hr, hl, hb₀⟩
  · exact .inr (.inl ⟨(Prod.mk.inj he).2, hr⟩)
  · exact .inr (.inr ⟨(Prod.mk.inj he).2, hr⟩)

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
