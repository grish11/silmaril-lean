module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.LaterCoreX
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.FirstKX

/-!
# The instantiation with node ends and the invariant (`Task.nodesRefX`)

* `nonCore_stepX`: `Multi.Nodes.nonCore_step` keeping `FrameRelX` (types resolved from the same
  definition, aliases of node exports at their core addresses, lifts of them, exports), the core
  store, the top-level calls, and the component functions up to appending;
* `later_runX`: `Multi.Nodes.later_run` with the node ends, carrying `FrameRelX` and the core
  instances of the nodes (`NodeAt`, kept as the shared core store grows);
* `nodesRefX_of`: **`Task.nodesRefX`** from `FirstKX` and `LaterCoreStepX`; `nodesRefX` (proved).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstCore
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
  Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.SingleThreaded (neverFail profile)

local notation "Σh" => Unit × List HLinked2.HostEvent

/-! ## The definitions other than core instantiations -/

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by cases h
  | (a', b') :: l, h => by
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hb
      cases h
      have : a = a' := by simpa using hb
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem forall₂_concat {α β : Type} {P : α → β → Prop} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : List.Forall₂ P l₁ l₂) (hab : P a b) : List.Forall₂ P (l₁ ++ [a]) (l₂ ++ [b]) :=
  List.rel_append h (.cons hab .nil)

/-- **A definition after the first core instantiation other than a core instantiation runs
silently**, keeping `FrameRelX`, the machine invariant, the core store and the top-level calls,
and appending only component functions. -/
theorem nonCore_stepX {pre : RefComponent} {R R' : RSt}
    {d : Syntax.Definition Silmaril.Wasm.Module} {sc : Scope (core3 neverFail)}
    {M : Machine.Config (core3 neverFail) Σh}
    (hpost : postDefOk (preLowers pre) (preInsts pre) (coreMods pre) d = true) (hni : ¬ IsInst d)
    (hR : refStep R d = some R') (hF : FrameRelX (coreMods pre) R sc M.store)
    (hL : LaterInv pre sc M) :
    ∃ sc' M', TRuns (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI) sc d) M sc' M' ∧
      FrameRelX (coreMods pre) R' sc' M'.store ∧ LaterInv pre sc' M' ∧ M'.host = M.host ∧
      M'.store.core = M.store.core ∧ (∃ fs, M'.store.funcs = M.store.funcs ++ fs) ∧
      M'.pending = M.pending ∧ M'.results = M.results ∧
      sc'.frame.coreInstances = sc.frame.coreInstances := by
  have hS0 : ∃ fs, M.store.funcs = M.store.funcs ++ fs := ⟨[], by simp⟩
  have hX0 : ∀ R'' : RSt, R''.coreInsts = R.coreInsts → ∃ X, R''.coreInsts = R.coreInsts ++ X :=
    fun R'' h => ⟨[], by simp [h]⟩
  cases d with
  | coreInstance ci =>
    cases ci with
    | instantiate => exact (hni trivial).elim
    | exports => simp [postDefOk] at hpost
  | type t =>
    cases t with
    | func ft =>
      have hft : funcTypePrim ft = true := by simpa [postDefOk] using hpost
      obtain ⟨ty, hty⟩ := resolveFuncType_prim sc.frame hft
      simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at hR
      obtain ⟨w, hw, rfl⟩ := hR
      erw [instDef_funcTypeG sc hty]
      have hF0 := hF.rel
      refine ⟨_, M, TRuns.pure _ M, ⟨⟨hF0.rmods, ?_, ?_, hF0.funcs_len, hF0.cf_len, hF0.ci⟩,
        forall₂_concat hF.types ⟨ty, rfl, ft, sc.frame, hft, hw, hty⟩, hF.coreFuncs, hF.funcs,
        hF.inline, hF.exports⟩, hL.frame rfl rfl, rfl, rfl, hS0, rfl, rfl, rfl⟩
      · simp [hF0.types_len]
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hF0.types_func x hx
        · simp at hx; exact ⟨_, hx⟩
    | _ => simp [postDefOk] at hpost
  | «alias» a =>
    cases a with
    | coreExport i n s =>
      cases s with
      | func =>
        have hnd : (coreMods pre).all (fun m => (m.exports.map (·.name)).Nodup) = true := by
          simpa [postDefOk] using hpost
        simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at hR
        obtain ⟨ci, hci, im, him, rfl⟩ := hR
        have hF0 := hF.rel
        obtain ⟨es, hes, hrel⟩ := forall₂_get hF0.ci hci
        obtain ⟨a, ha⟩ := cirel_lookup hnd hrel him
        erw [instDef_alias sc (es := es) hes ha rfl]
        have hnew : ∀ e, im = Impl.fwd e → EnvAddr R sc.frame.coreInstances e a := by
          intro e he
          subst he
          cases ci with
          | inline its =>
            exact absurd rfl (hF.inline i its hci _ (mem_of_lookup (by simpa [rciImpl] using him)))
          | node base exps =>
            simp only [rciImpl, Option.map_eq_some_iff] at him
            obtain ⟨j, hj, hje⟩ := him
            have hje' : e = base + j := by
              simp only [Impl.fwd, Impl.mk.injEq, Target.call.injEq, true_and] at hje
              exact hje.symm
            obtain ⟨hlt, hj', -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
            refine ⟨i, base, j, exps, es, n, exps[j].2, hci, hes, ?_, hje', ha⟩
            rw [List.getElem?_eq_getElem hlt]
            have : exps[j].1 = n := by simpa using hj'
            rw [← this]
        refine ⟨_, M, TRuns.pure _ M, ⟨⟨hF0.rmods, hF0.types_len, hF0.types_func, hF0.funcs_len,
          by rw [List.length_append, List.length_append, hF0.cf_len]; rfl, hF0.ci⟩, hF.types,
          forall₂_concat hF.coreFuncs hnew, hF.funcs, hF.inline, hF.exports⟩,
          hL.frame rfl rfl, rfl, rfl, hS0, rfl, rfl, rfl⟩
      | _ => simp [postDefOk] at hpost
    | _ => simp [postDefOk] at hpost
  | canon c =>
    cases c with
    | lift f opts t =>
      have hopts : opts = [] := by
        cases opts with
        | nil => rfl
        | cons _ _ => simp [postDefOk] at hpost
      subst hopts
      simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at hR
      obtain ⟨im, him, ft, hft, rfl⟩ := hR
      have hF0 := hF.rel
      obtain ⟨a, ha, hcf⟩ := forall₂_get hF.coreFuncs him
      obtain ⟨x, hx, ty, rfl, hty⟩ := forall₂_get hF.types hft
      erw [instDef_lift sc ha hx]
      have hS1 : ∃ fs, (ArenaOps.allocSt ArenaField.funcs (.lifted a ty {} ⟨0⟩) M.store).funcs =
          M.store.funcs ++ fs := ⟨[_], rfl⟩
      refine ⟨_, _, (TRuns.allocObj ArenaField.funcs (fun _ _ => rfl) _ M).bind (TRuns.pure _ _),
        ⟨⟨hF0.rmods, hF0.types_len, hF0.types_func, by simp [hF0.funcs_len], hF0.cf_len, hF0.ci⟩,
          hF.types, hF.coreFuncs, forall₂_concat
            (forall₂_imp_mono (fun x fid h => funcRelS_mono h hS1 (hX0 _ rfl) ⟨[], (List.append_nil _).symm⟩)
              hF.funcs) ?_, hF.inline,
          forall₂_imp_mono (fun x y ⟨fid, h1, h2⟩ =>
            ⟨fid, h1, funcRelS_mono h2 hS1 (hX0 _ rfl) ⟨[], (List.append_nil _).symm⟩⟩) hF.exports⟩,
        hL.congr rfl rfl (fs := [_]) rfl, rfl, rfl, hS1, rfl, rfl, rfl⟩
      intro ft' e he
      obtain ⟨he1, he2⟩ : ft' = ft ∧ im = Impl.fwd e := by
        obtain ⟨c, tg⟩ := im
        simp only [Impl.mk.injEq, List.cons.injEq, Adapter.lift.injEq] at he
        obtain ⟨⟨h1, h2⟩, h3⟩ := he
        subst h1 h2 h3
        exact ⟨rfl, rfl⟩
      subst he1
      refine ⟨a, ty, ?_, hty, hcf e he2, rfl⟩
      show (M.store.funcs ++ [_])[M.store.funcs.length]? = _
      simp
    | _ => simp [postDefOk] at hpost
  | export_ nm si ty =>
    obtain ⟨srt, k⟩ := si
    cases srt with
    | func =>
      cases ty with
      | none =>
        simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at hR
        obtain ⟨⟨im, ft⟩, hk, rfl⟩ := hR
        have hF0 := hF.rel
        obtain ⟨fid, hfid, hrelf⟩ := forall₂_get hF.funcs hk
        erw [instDef_funcExport sc hfid]
        refine ⟨_, M, TRuns.pure _ M, ⟨⟨hF0.rmods, hF0.types_len, hF0.types_func,
          by simp [hF0.funcs_len], hF0.cf_len, hF0.ci⟩, hF.types, hF.coreFuncs,
          forall₂_concat hF.funcs hrelf, hF.inline,
          forall₂_concat hF.exports ⟨fid, rfl, hrelf⟩⟩, hL.frame rfl rfl, rfl, rfl, hS0, rfl, rfl, rfl⟩
      | some _ => simp [postDefOk] at hpost
    | _ => simp [postDefOk] at hpost
  | _ => simp [postDefOk] at hpost

/-! ## The later definitions -/

/-- **The later definitions, then the end of the instantiation, with the node ends**: as
`later_run`, with `FrameRelX` and the core instances of the nodes (`NodeAt`) at the end, in the
configuration `Mf` before the end of the host's instantiation program. -/
theorem later_runX (h2 : LaterCoreStepX) {pre : RefComponent} :
    ∀ (ds : RefComponent) (R Rf : RSt) (sc : Scope (core3 neverFail))
      (M : Machine.Config (core3 neverFail) Σh)
      (K : Scope (core3 neverFail) → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail)))
      (L : List HLinked2.HostEvent) (ps : List (Binary.CoreMod × List Impl))
      (xs xs₀ : List NodeRun) (esN₀ : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr))),
      ds.foldlM refStep R = some Rf →
      ds.all (postDefOk (preLowers pre) (preInsts pre) (coreMods pre)) = true →
      (∃ X, Rf.nodes = R.nodes ++ X ∧ List.Forall₂ NodeW (coreNodes ps) X) →
      (∀ p ∈ ps, NodeOk p) →
      List.Forall₂ (fun q x => NodeEnd hostI.length q.1 q.2 x) ps xs →
      (∀ y ∈ (xs.map NodeRun.calls).flatten, y.2 = InstTests.unitV) →
      FrameRelX (coreMods pre) R sc M.store → LaterInv pre sc M → KFin K →
      sc.frame.coreInstances = instsVal (preInsts pre) ++ esN₀ →
      List.Forall₂ (NodeAt M.store.core) xs₀ esN₀ →
      M.ctl = [.ofProg none
        (ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc >>= K)] →
      M.host = ((), L) →
      ∃ (tr : List (Label (core3 neverFail) Σh)) (M' : Machine.Config (core3 neverFail) Σh)
        (scF : Scope (core3 neverFail)) (Mf : Machine.Config (core3 neverFail) Σh)
        (esN : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr))),
        Steps first.prof embL.hr (Host.ofEmbedder embL).dispatch M tr M' ∧
        (∀ ev, Label.host ev ∉ tr) ∧ M'.ctl = [] ∧ M'.store.lockdown = false ∧
        M'.host = ((), L ++ logOfCalls (xs.map NodeRun.calls).flatten) ∧
        (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, funcExports scF.exports) ∧
        FrameRelX (coreMods pre) Rf scF Mf.store ∧ LaterInv pre scF Mf ∧
        scF.frame.coreInstances = instsVal (preInsts pre) ++ esN ∧
        List.Forall₂ (NodeAt Mf.store.core) (xs₀ ++ xs) esN ∧
        Mf.pending = M.pending ∧ Mf.results = M.results ∧
        M' = { Mf with store := DispatchSt.decNestingSt Mf.store, ctl := [] }
  | [], R, Rf, sc, M, K, L, ps, xs, xs₀, esN₀, hfold, _, hX, _, hNC, _, hF, hL, hK, hci, hN, hc,
      hh => by
    simp only [List.foldlM_nil] at hfold
    cases hfold
    obtain ⟨X, hX, hW⟩ := hX
    have hX0 : X = [] := by simpa using hX.symm
    subst hX0
    have hps : ps = [] := by
      cases ps with
      | nil => rfl
      | cons _ _ => cases hW
    subst hps
    cases hNC
    have hc' : M.ctl = [.ofProg none (K sc)] := by rw [hc]; rfl
    obtain ⟨tr, M', hs, hn, hctl, hlock, hhost, -, hobs, hM'⟩ := hK sc M hL.lock hc'
    exact ⟨tr, M', sc, M, esN₀, hs.steps, hn, hctl, hlock, by rw [hhost, hh]; simp [logOfCalls], hobs,
      hF, hL, hci, by simpa using hN, rfl, rfl, hM'⟩
  | d :: ds, R, Rf, sc, M, K, L, ps, xs, xs₀, esN₀, hfold, hpost, hX, hok, hNC, hu, hF, hL, hK,
      hci, hN, hc, hh => by
    simp only [List.foldlM_cons] at hfold
    cases hR : refStep R d with
    | none => rw [hR] at hfold; cases hfold
    | some R₁ =>
    rw [hR] at hfold
    simp only [List.all_cons, Bool.and_eq_true] at hpost
    obtain ⟨hd, hpost⟩ := hpost
    obtain ⟨X, hX, hW⟩ := hX
    obtain ⟨Y, hY, -⟩ := foldlM_refStep_nodes hfold
    by_cases hi : IsInst d
    · -- a core instantiation
      obtain ⟨mi, cargs, rfl⟩ : ∃ mi cargs, d = .coreInstance (.instantiate mi cargs) := by
        cases d with
        | coreInstance ci => cases ci with
          | instantiate mi cargs => exact ⟨mi, cargs, rfl⟩
          | exports => exact hi.elim
        | _ => exact hi.elim
      obtain ⟨m, nm, imps, exps, w, hm, hci', hRn, -⟩ := refStep_inst hR
      have hm' : (coreMods pre)[mi]? = some m := by rw [← hF.rel.rmods]; exact hm
      have hXY : X = (m, w) :: Y := by
        rw [hY, hRn] at hX
        simpa using hX.symm
      subst hXY
      obtain ⟨p, ps', rfl, hpW, hW'⟩ : ∃ p ps', ps = p :: ps' ∧ NodeW (.core p.1 p.2) (m, w) ∧
          List.Forall₂ NodeW (coreNodes ps') Y := by
        cases ps with
        | nil => cases hW
        | cons p ps' => cases hW with | cons h1 h2 => exact ⟨p, ps', rfl, h1, h2⟩
      obtain ⟨cm, he, hdec, hcif⟩ := hpW
      injection he with he₁ he₂
      subst he₁
      have hmod : Binary.coreModule p.1 = m := by
        unfold Binary.coreModule
        rw [hdec]
        rfl
      have hilen : (CoreModule.imports p.1).length = m.imports.length :=
        (FirstImp.coreIface_imports_length hcif).symm ▸ rfl
      obtain ⟨nx, xs', rfl, ht, hNC'⟩ : ∃ nx xs', xs = nx :: xs' ∧
          NodeEnd hostI.length p.1 p.2 nx ∧
          List.Forall₂ (fun q x => NodeEnd hostI.length q.1 q.2 x) ps' xs' := by
        cases hNC with | cons h1 h2 => exact ⟨_, _, rfl, h1, h2⟩
      simp only [List.map_cons, List.flatten_cons, List.mem_append] at hu
      obtain ⟨tr₁, M₁, sc₁, g, d₁, hn₁, -, hob₁, hc₁, hL₁, hh₁, -, hci₁, hcf₁, hex₁, hE, hty₁, hfn₁,
          hgpre, hPre, hcore₁, hfs₁, hpend₁, hres₁⟩ :=
        h2 pre mi cargs ds sc M m p nx L K hm' hd hmod hilen (hok p List.mem_cons_self) ht
          (fun y hy => hu y (.inl hy)) hL hc hh
      have hF₁ := frameRelX_inst hF hR hm' hci₁ hcf₁ hty₁ hfn₁ hex₁ hE hfs₁
      have hN₁ : List.Forall₂ (NodeAt M₁.store.core) (xs₀ ++ [nx])
          (esN₀ ++ ([(core3 neverFail).exports (g.sh.minst nx.minst)] :
            List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr)))) := by
        refine forall₂_concat (forall₂_imp_mono (fun x es h => ?_) hN)
          ⟨g, hPre, ⟨{}, by rw [store_app_nil]; exact hcore₁⟩, rfl⟩
        rw [hcore₁, show g.rel _ = Store.app g.pre _ from rfl, hgpre]
        exact nodeAt_app h _
      obtain ⟨tr₂, M₂, scF, Mf, esN, d₂, hn₂, hctl, hlock, hhost, hobs, hFf, hLf, hcif', hNf,
          hpf, hrf, hM₂⟩ :=
        later_runX h2 ds _ Rf sc₁ M₁ K (L ++ logOfCalls nx.calls) ps' xs' (xs₀ ++ [nx])
          (esN₀ ++ ([(core3 neverFail).exports (g.sh.minst nx.minst)] :
            List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr)))) hfold hpost ⟨Y, hY, hW'⟩
          (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hNC' (fun y hy => hu y (.inr hy))
          hF₁ hL₁ hK (by rw [hci₁, hci]; exact List.append_assoc _ _ _) hN₁ hc₁ hh₁
      refine ⟨tr₁ ++ tr₂, M₂, scF, Mf, esN, Adequacy.steps_append d₁.steps d₂, ?_, hctl, hlock,
        ?_, ?_, hFf, hLf, hcif', by simpa using hNf, hpf.trans (hpend₁), hrf.trans hres₁, hM₂⟩
      · intro ev hev
        rcases List.mem_append.mp hev with h | h
        · exact hn₁ ev h
        · exact hn₂ ev h
      · rw [hhost, List.map_cons, List.flatten_cons, logOfCalls_append, List.append_assoc]
      · have h₁ : (tr₁.filterMap Label.obs?) = [] := hob₁
        simp only [traceObs, List.filterMap_append, h₁, List.nil_append] at hobs ⊢
        exact hobs
    · -- another definition
      obtain ⟨sc₁, M₁, hT, hF₁, hL₁, hh₁, hcore₁, hfs₁, hpend₁, hres₁, hci₁⟩ :=
        nonCore_stepX hd hi hR hF hL
      obtain ⟨tr₁, hq, htau⟩ := sruns_tau (dispatch := DG embL.host) hT none rfl
      have d₁ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) hq hL.lock
        (fun sc' => ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc' >>= K)
        (segs := []) (rest := []) (by rw [hc, ctl_cons]; rfl)
      obtain ⟨Y₁, hY₁, hY₁'⟩ := refStep_nodes hR
      have hY0 := hY₁' hi
      subst hY0
      obtain ⟨tr₂, M₂, scF, Mf, esN, d₂, hn₂, hctl, hlock, hhost, hobs, hFf, hLf, hcif', hNf,
          hpf, hrf, hM₂⟩ :=
        later_runX h2 ds R₁ Rf sc₁ { M₁ with ctl := [.ofProg none
          (ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc₁ >>= K)] }
          K L ps xs xs₀ esN₀ hfold hpost
          ⟨X, by rw [hX, hY₁, List.append_nil], hW⟩ hok hNC hu hF₁
          (hL₁.congr rfl rfl (fs := []) (by simp)) hK (by rw [hci₁, hci])
          (by rw [show ({ M₁ with ctl := _ } : Machine.Config (core3 neverFail) Σh).store.core =
            M.store.core from hcore₁]; exact hN) rfl (by rw [← hh, ← hh₁])
      refine ⟨tr₁ ++ tr₂, M₂, scF, Mf, esN, Adequacy.steps_append d₁.steps d₂, ?_, hctl, hlock,
        hhost, ?_, hFf, hLf, hcif', hNf, hpf.trans hpend₁, hrf.trans hres₁, hM₂⟩
      · intro ev hev
        rcases List.mem_append.mp hev with h | h
        · exact absurd (htau _ h) (by simp)
        · exact hn₂ ev h
      · rw [traceObs, List.filterMap_append]
        have := traceObs_tau htau
        simp only [traceObs] at this
        rw [this, List.nil_append]
        exact hobs

/-! ## The instantiation -/

/-- **`Task.nodesRefX` from the first node and the later core instantiations.** -/
theorem nodesRefX_of (h1 : FirstKX) (h2 : LaterCoreStepX) : Task.nodesRefX := by
  intro b c r ps xs hpc hr hf himp hnodes hu hNC
  obtain ⟨-, hw, -, pre, mi, cargs, post, hs, -, hpostOk⟩ := multiImpFrag_inv hf
  obtain ⟨p, ps', rfl⟩ := nodes_ne_nil hpc hr hf hnodes
  have hok := nodeOk_frag hpc hr hf hnodes
  cases hNC with
  | @cons _ x₀ _ xs' h₀ hNC' =>
  simp only [List.map_cons, List.flatten_cons, List.mem_append] at hu
  obtain ⟨sc, M, ⟨-, ⟨K, hK, hc⟩, -, hh⟩, hL, hpend, hres, ⟨tr₀, hs₀, hn₀, hob₀⟩,
      ⟨es₀, hci₀, hN₀⟩, hFR⟩ :=
    h1 b c r p ps' x₀ pre mi cargs post hpc hr hf himp hnodes (fun y hy => hu y (.inl hy)) h₀ hs
  obtain ⟨R, hR, -, -, hN⟩ := relW_of_decode hpc hr (inFrag_of_hostWired hw)
  have hRr : refRead r = some R := hR
  rw [hnodes] at hN
  have hrr := firstCore?_eq r hs
  unfold refRead at hR
  have hsplit : r = (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]) ++ post := by
    rw [hrr]; simp
  rw [hsplit, foldlM_option_append] at hR
  cases hR₀ : (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
      ({ env := (r.filter isFuncImport).length } : RSt) with
  | none =>
    rw [← hsplit, hR₀] at hR
    cases hR
  | some R₀ =>
  rw [← hsplit, hR₀] at hR
  simp only [Option.bind_some] at hR
  have hFR₀ := hFR R₀ hR₀
  rw [foldlM_option_append] at hR₀
  cases hR₁ : pre.foldlM refStep ({ env := (r.filter isFuncImport).length } : RSt) with
  | none => rw [hR₁] at hR₀; cases hR₀
  | some R₁ =>
  rw [hR₁] at hR₀
  simp only [Option.bind_some, List.foldlM_cons, List.foldlM_nil] at hR₀
  obtain ⟨Y₁, hY₁, hY₁'⟩ := foldlM_refStep_nodes hR₁
  have hY₁0 := hY₁' (firstCore?_noInst r hs)
  subst hY₁0
  cases hci : refStep R₁ (.coreInstance (.instantiate mi cargs)) with
  | none => rw [hci] at hR₀; cases hR₀
  | some R₂ =>
  rw [hci] at hR₀
  have hR₀' : R₂ = R₀ := by simpa using hR₀
  subst hR₀'
  obtain ⟨m0, -, -, -, w0, -, -, hn2, -⟩ := refStep_inst hci
  obtain ⟨X, hX, -⟩ := foldlM_refStep_nodes hR
  rw [hX, hn2, hY₁] at hN
  simp only [List.append_nil] at hN
  have hN' : List.Forall₂ NodeW (coreNodes ps') X := by
    simp only [List.nil_append, List.singleton_append] at hN
    cases hN with | cons _ h => exact h
  obtain ⟨tr₁, M', scF, Mf, esN, d, hn₁, hctl, hlock, hhost, hobs, hFf, hLf, hcif, hNf, hpf, hrf,
      hM'⟩ :=
    later_runX h2 post _ R sc M K (logOfCalls x₀.calls) ps' xs' [x₀] [es₀] hR hpostOk ⟨X, hX, hN'⟩
      (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hNC' (fun y hy => hu y (.inr hy))
      hFR₀ hL hK hci₀ (.cons hN₀ .nil) hc hh
  have hS : M'.store.funcs = Mf.store.funcs := by rw [hM']; rfl
  have hC : M'.store.core = Mf.store.core := by rw [hM']; rfl
  refine ⟨M', ⟨0⟩, funcExports scF.exports, ⟨tr₀ ++ tr₁, Adequacy.steps_append hs₀ d, ?_, hctl,
    hlock, ?_⟩, ?_, ?_⟩
  · intro ev hev
    rcases List.mem_append.mp hev with h | h
    · exact hn₀ ev h
    · exact hn₁ ev h
  · have h₀ : tr₀.filterMap Label.obs? = [] := hob₀
    simp only [traceObs, List.filterMap_append, h₀, List.nil_append] at hobs ⊢
    exact hobs
  · rw [hhost, List.map_cons, List.flatten_cons, logOfCalls_append]
  · refine ⟨rfl, hctl, hlock, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hM']
      show Mf.store.nestingDepth - 1 = 0
      rw [hLf.depth]
    · rw [hM']; exact hLf.inst
    · rw [hM']; exact hLf.func0
    · rw [hM']; exact ⟨hpf.trans hpend, hrf.trans hres⟩
    · rw [hC]; exact ⟨hLf.ok, hLf.hosts⟩
    · exact ⟨R, scF, pre, mi, cargs, post, esN, hRr, hs, rfl, frameRelX_funcs hFf hS, hcif,
        by rw [hC]; exact hNf⟩

/-- **The instantiation on the fragment, with node ends and the invariant.** -/
theorem nodesRefX : Task.nodesRefX := nodesRefX_of firstKX laterCoreStepX

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
