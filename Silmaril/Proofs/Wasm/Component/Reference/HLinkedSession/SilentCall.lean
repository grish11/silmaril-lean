module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Round
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.Silent
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd.Call

/-!
# A call of `HLinked2.toRef` under a host that never answers

`silent_call`: from a configuration between calls (`ReadyL P l.toW`, `HStat`), a typed call
whose specification round (`SessRound.Ok`, the instance's path, the component import calls an
`HLinked2.ExpRunH`) makes a host call runs, under `HLinked2.silentHost`, to a trap of reason
`cannotBlockSync`, with no host event and no other trap on the way:

1. the host's invocation and the deterministic prefix of the importer's lifted export
   (`call_atLKTS`);
2. the importer's core activation, with its returned nested calls to the exporter, up to the
   callout of its first host call (`rounds_toHost`, `kseg_run`);
3. the callout program (`blocks_callout_silent`): the host function takes the arguments and
   returns without resolving the subtask; `canon_lower` waits on it and the thread blocks;
4. the synchronous lift loop of the call (`CallAtLKTS.block`): the call's task is unresolved and
   the only thread of the importer's instance is not ready, so it traps `cannotBlockSync`.

`hlinked2_silent_cannotBlock` places this at the first call after `HLinked2.instantiates`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own)

variable {P : Profile} {σ : Type} {prof : ProfileKind}

/-! ## No ready thread -/

/-- A thread that started waiting on `rc` and blocked is not ready while `rc` does not hold. -/
theorem threadReady_blocked (hr : Nat → Bool) (s : CStore (E3 P)) (t : ThreadId)
    (rc : ReadyCond)
    (hrc : rc.eval hr (threadStatusSt t .blocked (CStore.startWaitingSt t rc s)) = false) :
    (threadStatusSt t .blocked (CStore.startWaitingSt t rc s)).threadReady hr t = false := by
  have e : ArenaField.threads.get? (threadStatusSt t .blocked (CStore.startWaitingSt t rc s)) t =
      (ArenaField.threads.get? s t).map
        (fun th => { { th with readyCond := some rc } with status := .blocked }) := by
    show ArenaField.threads.get? (ArenaField.threads.modify (CStore.startWaitingSt t rc s) t
      fun th => { th with status := .blocked }) t = _
    rw [ArenaField.get?_modify_self]
    show Option.map _ (ArenaField.threads.get? (ArenaField.threads.modify s t
      fun th => { th with readyCond := some rc }) t) = _
    rw [ArenaField.get?_modify_self, Option.map_map]
    rfl
  unfold CStore.threadReady CStore.threadIs CStore.thread?
  rw [e]
  rcases ArenaField.threads.get? s t with _ | th
  · rfl
  · simp only [Option.map_some, Runtime.Thread.ready, Runtime.Thread.blocked, hrc,
      Bool.and_false]

/-- The instance `2` holding only thread `t`, which is not ready, has no candidate. -/
theorem instCandidates_enter {hr : Nat → Bool} {s : CStore (E3 P)} {ι : InstState}
    {t : ThreadId} (hi : s.inst? ⟨2⟩ = some (enterInst ι t)) (ht : s.threadReady hr t = false) :
    s.instCandidates hr ⟨2⟩ = [] := by
  unfold CStore.instCandidates
  rw [hi]
  simp [enterInst, Table.elements, ht]

/-! ## The call -/

section Call

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {B₀ : Machine.Config (E3 P) σ}
  {fs : List (CFuncInst (core3P P))}

/-- **A call whose round makes a host call traps `cannotBlockSync` under the silent host**:
from the invocation, a run without host events and without other traps, then the trap
`cannotBlockSync`, which locks the store down. -/
theorem silent_call (S₀ : HStat P l Ie Ii u₀ F₀ B₀ (ownOf s₀)) (hB₀ : B₀.store.funcs = fs)
    (hfs : LiftedOkH l Ii s₀ fs) {cs : (core3P P).Store (CanonHost (core3P P))}
    {ιe ιi : InstState} {G : Garb P σ} {ST : List Subtask} {h₀ : σ} {k : Nat} {u π : Store Nat}
    (R : ReadyL P l.toW Ie Ii s₀ u₀ F₀ cs ιe ιi G u π k) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Store Nat} (hpath : Ii.Path P (.idle u) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie π d.dss.flatten π₁)
    (hh : l.hostCalls d.dss.flatten ≠ []) :
    ∃ (tr : List (Label (E3 P) σ)) (m' : Machine.Config (E3 P) σ),
      Steps prof (fun _ _ => false) (DI P HLinked2.silentImpl)
        (invokedAtL cs ιe ιi fs G ST h₀ k (l.host.length + l.exp.exports.length + d.j)
          (d.vs.map toRefVal))
        (tr ++ [.trap .cannotBlockSync]) m' ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ m'.store.lockdown = true := by
  obtain ⟨xs, hck, hf₁, hf₂, hrel⟩ := hok
  have hvs : ValTy.checkList l.imp.exports[d.j].ty.params d.vs = true := by
    unfold checkLower at hck
    split_ifs at hck with h
    exact h
  have hxs : xs = lowerArgs l.imp.exports[d.j].ty.params d.vs := by
    simp only [checkLower, hvs, ↓reduceIte, Option.some.injEq] at hck
    exact hck.symm
  subst hxs
  have hx : l.imp.exports[d.j] ∈ l.imp.exports := List.getElem_mem d.j.isLt
  obtain ⟨hmax, hmaxr, hres⟩ := S₀.arity.1 _ hx
  obtain ⟨hpf, hrf⟩ := S₀.floats.1 _ hx
  have ha : Ii.addrs.getD l.imp.exports[d.j].core 0 = Ii.addr d.f.1 := by
    rw [← hf₁]
    rfl
  have hfj : fs[l.host.length + l.exp.exports.length + d.j]? =
      some (.lifted (s₀.funcs.length + Ii.addr d.f.1) (liftedFt l.imp.exports[d.j]) {} ⟨2⟩) :=
    ha ▸ hfs d.j
  obtain ⟨M₀, th, K, segs, rest, tr₁, hpre, hat⟩ := call_atLKTS (impl := HLinked2.silentImpl)
    prof cs ιe ιi fs G ST h₀ k (l.host.length + l.exp.exports.length + d.j) _
    l.imp.exports[d.j] d.vs hpf hvs hmax hres hmaxr hrf R.thI R.leave hfj
  have S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀) := S₀.move R.inv.wfI (hat.funcs.trans hB₀.symm)
  have hI₀ : LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) d.f
      (cs, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (s₀.funcs.length + Ii.addr d.f.1)
        (lowerArgs l.imp.exports[d.j].ty.params d.vs)) (u, Ii.initThread d.f) π :=
    linv_ready R.inv hf₂ rfl
  have hpath' : Ii.Path P (.running d.f u (Ii.initThread d.f))
      (callMoves d.cs ++ [.inr (.ans d.f d.w)]) (.idle u₁) := by
    have h : Ii.Path P (.idle u) (.inr (.ask d.f) :: (callMoves d.cs ++ [.inr (.ans d.f d.w)]))
        (.idle u₁) := hpath
    cases h with
    | cons h₁ h₂ =>
      cases h₁
      exact h₂
  obtain ⟨recs, yc, i, hi, ys, ws, hseg, hst, hys, hws⟩ := rounds_toHost S d.cs d.dss _
    (u, Ii.initThread d.f) π π₁ u₁ hI₀ hrel hexp hpath' hh
  -- the importer's segmented run, to the host callout
  have hlive₀ : Live M₀ := by
    rw [hat.start]
    exact coreCfg_extN_live _ _ _ _ _ _ _ _ _
  obtain ⟨ιe', N', C', tr₂, -, hq₂, r₂⟩ := kseg_run (prof := prof)
    (impl := HLinked2.silentImpl) (K := K) (segs := segs) (rest := rest) hat.frame hseg ιe []
    M₀.conts R.thE
  have r₁₂ : Steps prof (fun _ _ => false) (DI P HLinked2.silentImpl)
      (invokedAtL cs ιe ιi fs G ST h₀ k (l.host.length + l.exp.exports.length + d.j)
        (d.vs.map toRefVal))
      (tr₁ ++ tr₂) (coreCfg (extN M₀ ιe' N' C') th K segs rest yc) := by
    refine Adequacy.steps_append hpre.steps ?_
    rw [← hat.start] at r₂
    exact r₂
  have hq₁₂ : Quiet (tr₁ ++ tr₂) := (Quiet.of_lrun hpre hlive₀).append hq₂
  have hth := hat.thread
  subst hth
  -- the callout step
  have hent := hat.frame.entry ⟨i⟩ (witFt l.host[i].2) ιe' N' C'
  obtain ⟨ι₂, hι₂, hleave⟩ := hat.frame.inst2 ιe' N' C'
  have hmem : l.host[i] ∈ l.imp.imports := by
    have h₁ : l.host[i] ∈ l.imp.imports.drop l.wire.length := by
      rw [S.wireTy.shape.1]
      exact List.getElem_mem hi
    exact List.mem_of_mem_drop h₁
  obtain ⟨hmaxp, -, -⟩ := S.arity.2 _ hmem
  obtain ⟨hpfi, -⟩ := S.floats.2 _ hmem
  let M₁ := coreCfg (extN M₀ ιe' N' C') (some ⟨G.threads.length⟩) K segs rest yc
  have s₃ : Step prof (fun _ _ => false) (DI P HLinked2.silentImpl) M₁ .tau
      { M₁ with ctl := ⟨some ⟨G.threads.length⟩,
        .prog (DI P HLinked2.silentImpl
          (.hostCallout (.lowered ⟨i⟩ (witFt l.host[i].2) {} ⟨2⟩) ys)),
        .core yc.2 K :: segs⟩ :: rest } :=
    Step.coreCallout rfl hst
  -- the callout program blocks
  obtain ⟨pos, trB, hB⟩ := blocks_callout_silent (t := ⟨G.threads.length⟩) (m := M₁) hent hι₂
    hleave (S.hostFn i hi) hpfi hys hmaxp hws
  obtain ⟨kB, segsB, rB⟩ := hB.lrun (prof := prof) (hr := fun _ _ => false) rfl Prog.pure
    (.core yc.2 K :: segs) rest
  rw [Prog.bind_eq, Prog.bind_pure] at rB
  let mB : Machine.Config (E3 P) σ :=
    { M₁ with store := silentSt M₁.store ⟨2⟩ ys l.host[i].2 pos ⟨G.threads.length⟩ }
  have hlB : Live ({ mB with ctl := ⟨some ⟨G.threads.length⟩,
      .prog (.op (S := Eff (E3 P) σ) (.block none) kB), segsB⟩ :: rest } : Machine.Config (E3 P) σ) :=
    ⟨List.cons_ne_nil _ _, rfl⟩
  let M₂ : Machine.Config (E3 P) σ :=
    { (mB.setCont ⟨G.threads.length⟩ (some (blockedAct ⟨G.threads.length⟩ kB segsB))) with
      store := threadStatusSt ⟨G.threads.length⟩ .blocked mB.store, ctl := rest }
  have s₄ : Step prof (fun _ _ => false) (DI P HLinked2.silentImpl)
      { mB with ctl := ⟨some ⟨G.threads.length⟩,
        .prog (.op (S := Eff (E3 P) σ) (.block none) kB), segsB⟩ :: rest } .tau M₂ :=
    Step.block rfl
  -- the synchronous lift loop traps
  have hready : M₂.store.threadReady (fun _ => false) ⟨G.threads.length⟩ = false :=
    threadReady_blocked _ _ _ _ (silent_unresolved M₁.store ⟨2⟩ ys l.host[i].2 pos)
  have hinst : M₂.store.inst? ⟨2⟩ = some (enterInst ιi ⟨G.threads.length⟩) := by
    show (extN M₀ ιe' N' C').store.insts[2]? = _
    simp [extN, hat.insts]
    rfl
  have htasks : M₂.store.tasks = G.tasks ++
      [(taskK₁ l.imp.exports[d.j] G.callers ⟨G.threads.length⟩).withState .started] ++
        N'.map (·.task) := by
    show (extN M₀ ιe' N' C').store.tasks = _
    simp [extN, hat.tasks]
  obtain ⟨tr₃, mT, r₃, hl₃, hu₃, -⟩ := hat.block M₂ _ _ rfl rfl htasks (by
      intro h
      cases h) (instCandidates_enter hinst hready)
  -- assembly
  have hqB : Quiet trB := Quiet.of_lrun rB hlB
  have hq₃ : Quiet tr₃ := Quiet.of_lrun r₃ hl₃
  have hall : Quiet ((tr₁ ++ tr₂) ++ (.tau :: (trB ++ (.tau :: tr₃)))) :=
    hq₁₂.append (Quiet.tau.append (hqB.append (Quiet.tau.append hq₃)))
  refine ⟨(tr₁ ++ tr₂) ++ (.tau :: (trB ++ (.tau :: tr₃))), trapCfg mT, ?_, hall.1, hall.2, rfl⟩
  have r : Steps prof (fun _ _ => false) (DI P HLinked2.silentImpl)
      (invokedAtL cs ιe ιi fs G ST h₀ k (l.host.length + l.exp.exports.length + d.j)
        (d.vs.map toRefVal))
      ((tr₁ ++ tr₂) ++ (.tau :: (trB ++ (.tau :: (tr₃ ++ [.trap .cannotBlockSync])))))
      (trapCfg mT) :=
    Adequacy.steps_append r₁₂ (.cons s₃ (Adequacy.steps_append rB.steps
      (.cons s₄ (Adequacy.steps_append r₃.steps (.cons hu₃.1 (.refl _))))))
  simpa only [List.append_assoc, List.cons_append] using r

end Call


/-! ## After instantiation -/

/-- The export map of the instantiated `l.toRef` finds the importer's export `j` at function
`host.length + exp.exports.length + j`. -/
theorem exportMapH_lookup {l : HLinked2} (hIg : l.imp.Good) (j : Fin l.imp.exports.length) :
    l.exportMap.lookup l.imp.exports[j].name =
      some ⟨l.host.length + l.exp.exports.length + j⟩ :=
  lookup_mapIdx_val (·.name) (fun i => (⟨i⟩ : FuncId)) (l.host.length + l.exp.exports.length)
    l.imp.exports j j.isLt hIg.names

/-- **The first call after instantiation, under the silent host** (`silent_call` at the
configuration of `HLinked2.instantiates`): a typed call whose specification round from the
instances' stores makes a host call traps `cannotBlockSync`. -/
theorem hlinked2_silent_cannotBlock (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Store Nat} (hpath : Ii.Path P (.idle Ii.store) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie Ie.store d.dss.flatten π₁)
    (hh : l.hostCalls d.dss.flatten ≠ []) :
    ∃ m : Machine.Config (core3P P) σ, m.ctl = [] ∧ m.host = h₀ ∧
      InstResult.instance m ⟨0⟩ l.exportMap ∈ instBehaviours prof (HLinked2.silentHost P)
        (LinkedSession.hostConfig l.host h₀) l.toRef (importArgs l.host) ∧
      ∃ (tr : List (Label (core3P P) σ)) (m' : Machine.Config (core3P P) σ),
        Steps prof (HLinked2.silentHost P).hr (HLinked2.silentHost P).dispatch m
          (.host (.invoke ⟨0⟩ ⟨l.host.length + l.exp.exports.length + d.j⟩
            (d.vs.map toRefVal)) :: (tr ++ [.trap .cannotBlockSync])) m' ∧
        (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ m'.store.lockdown = true := by
  obtain ⟨hEg, hEi, hIg, hIi', har, hff, hW, hN, hn, hS⟩ := hl
  obtain ⟨Ie₀, cse, cie, hFe⟩ := coreFacts (Pf := P) hEg hEi
  obtain rfl : Ie = Ie₀ := NumModule.IsInst.unique hIe hFe.isInst
  obtain ⟨r, cii, hrs, hh', hFi⟩ := coreFactsH_of_inst (Pf := P) hIg hIi'
    ⟨hS.imp.data, hS.imp.elems⟩ hIi cse
  have hmem := instH_mem hEg hFe hIg har hIi'.importNames hW hN hFi prof (HLinked2.silentHost P) h₀
  have S₀ : HStat P l Ie Ii Ii.store
      (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)).funcs
      (readyCfgL (σ := σ) (reloc (cse : Store (CanonHost (E3 P))) (Store.mapH Prod.fst r)) {} {}
        (funcsH l Ie (liftedList (addrL (cse : Store _).funcs.length Ii) ⟨2⟩ l.imp.exports))
        Garb.empty [] h₀)
      (ownOf Ie.store) :=
    hstat_init hEg hIg hW hn har hff hFe hIi hh' _ rfl
  have R₀ := readyH_init (σ := σ) hS hn hW hFe hIi hrs hh'
  obtain ⟨tr, m', hsteps, hq₁, hq₂, hlock⟩ := silent_call (prof := prof) (ST := []) (h₀ := h₀)
    S₀ rfl (liftedOkH_afterLink hIi hIg hFe) R₀ d hok hpath hexp hh
  refine ⟨afterLinkH P (reloc cse (Store.mapH Prod.fst r)) (fun k => Ie.addrs.getD k 0)
    (addrL (cse : Store _).funcs.length Ii) l h₀, rfl, rfl, hmem, tr, m', ?_, hq₁, hq₂, hlock⟩
  exact .cons (invoke_stepL (impl := HLinked2.silentImpl) R₀.fresh _ _) hsteps

/-- **The session of one such call, under the silent host, answers a trap** (`silentObs`). -/
theorem hlinked2_silent_session (P : Profile) (prof : ProfileKind) {l : HLinked2}
    (hl : l.Adequate) {σ : Type} (h₀ : σ) {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hIe : l.exp.mod.IsInst Ie) (hIi : l.imp.mod.IsInst Ii) (d : Linked2.SessRound l.toL2 Ii)
    (hok : d.Ok) {u₁ π₁ : Store Nat} (hpath : Ii.Path P (.idle Ii.store) d.instMoves (.idle u₁))
    (hexp : HLinked2.ExpRunH P l Ie Ie.store d.dss.flatten π₁)
    (hh : l.hostCalls d.dss.flatten ≠ []) :
    ∃ s : σ, ([none], s) ∈ HLinked2.silentObs P prof l h₀ [(d.j, d.vs)] := by
  obtain ⟨m, -, -, hmem, tr, m', hsteps, hq₁, hq₂, hlock⟩ :=
    hlinked2_silent_cannotBlock P prof hl h₀ hIe hIi d hok hpath hexp hh
  have hc : Calls prof (HLinked2.silentHost P).hr (HLinked2.silentHost P).dispatch m ⟨0⟩
      ⟨l.host.length + l.exp.exports.length + d.j⟩ (d.vs.map toRefVal) m' .trap := by
    refine ⟨tr ++ [.trap .cannotBlockSync], hsteps, ?_, ?_, hlock⟩
    · intro ev hm
      rcases List.mem_append.mp hm with hm | hm
      · exact absurd hm (hq₁ ev)
      · simp at hm
    · intro _ msg hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hq₂ _ hm
      · simp at hm
  refine ⟨(resumeCfg m m').host, m, ⟨0⟩, l.exportMap,
    [⟨l.host.length + l.exp.exports.length + d.j⟩], resumeCfg m m', hmem, ?_, ?_, rfl⟩
  · simp only [HLinked2.refCalls, List.map_cons, List.map_nil, List.mapM_cons, List.mapM_nil,
      exportMapH_lookup hl.impGood d.j]
    rfl
  · exact .trap hc (.nil _ _)

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
