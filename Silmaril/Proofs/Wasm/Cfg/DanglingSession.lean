module

public import Silmaril.Wasm.Cfg.DanglingSession.Defs
public import Silmaril.Wasm.Cfg.DanglingBack.Thms
public import Silmaril.Wasm.Cfg.ExampleAlias.Thms
public import Silmaril.Wasm.Interp.EHSim.Thms
public import Silmaril.Proofs.Wasm.Cfg.DanglingBack
public import Silmaril.Proofs.Wasm.Cfg.DanglingExnFwd
public import Silmaril.Proofs.Wasm.Cfg.ExampleAlias

@[expose] public section

/-!
# Threaded sessions with dangling host exceptions (proofs)

1. **What a round changes in the real store.** A host-free Core step keeps the store's functions
   and tags, only appends exceptions (`Step.throw`, at `s.exns.length`), and keeps the tag
   invariants `TagsOk tags` (`step_store`). The universal hosts `instHostQ I Q` keep the whole
   store, so along a labelled run the same holds (`evRunQ_store`).
2. **The relaxed domain is kept by every round** of the instance triple (`domD_of_round`): the
   round is a labelled Core run of a question entering `ConfigOkD` (`configOkD_of_domD`) at the
   unrestricted host (`CfgInst.evRun_Q_iff`, the store's host functions being typed imports), so
   its end store satisfies `StoreOkD` (`ConfigOkD.evRun`, `storeOkD_of_configOkD`), and the
   functions, tags, checker acceptance and real `ExnsOk` are carried by item 1.
3. **Per question on the domain**, both inclusions (`sub_cfgInstTripleU`, `cfgInstTripleU_sub`):
   the proofs of `DanglingBack.instTripleS_sub_cfgInstTripleU` and
   `DanglingExn.cfgInstTripleU_sub`, which read of `WellFormed`/`InstDom` only what `InstDomD`
   provides.
4. **Sessions**: `threadS_eq_of_agree` at every reachable store.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingSession

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Cfg.CfgInst Silmaril.Wasm.Cfg.DanglingExn Silmaril.Wasm.Cfg.DanglingBack
open Silmaril.Wasm.Cfg.DanglingSession
open Silmaril.Wasm.Abstract (wasmHostSig coreHostRel CoreBehSXP EvRun HEvStep)
open Silmaril.Wasm.Abstract.NodeBridge (instHost qOf viewTriple CoreCallout)
open Silmaril.Wasm.Abstract.InstSession (instTripleS instSession)
open Silmaril.Wasm.Interp (TagsOk StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Games.Abstract.StratThread (Reach)

/-! ## 1. What a round changes in the real store -/

section Store

variable {H : Type} {P : Numerics.Profile} {tags : List TagInst}

/-- **A host-free Core step keeps the functions and the tags, only appends exceptions, and keeps
the tag invariants.** -/
theorem step_store {c c' : Config H} (h : Step P (fun _ _ _ _ => False) c c') :
    c'.store.funcs = c.store.funcs ∧ c'.store.tags = c.store.tags ∧
      c.store.exns <+: c'.store.exns ∧ (TagsOk tags c.store → TagsOk tags c'.store) := by
  refine ⟨(SingleThreaded.Step.framesLocal h).1, Proofs.CfgInst.step_tags_eq h, ?_⟩
  induction h with
  | «variable» h => cases h <;> exact ⟨List.prefix_refl _, id⟩
  | table h => cases h <;> exact ⟨List.prefix_refl _, id⟩
  | memory h => cases h <;> exact ⟨List.prefix_refl _, id⟩
  | reference h => cases h <;> exact ⟨List.prefix_refl _, id⟩
  | aggregate h => cases h <;> exact ⟨List.prefix_refl _, id⟩
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | ctxtFrame _ ih => exact ih
  | throw ht he hn => exact ⟨List.prefix_append _ _, fun hT => Interp.tagsOk_throw hT ht he hn⟩
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | _ => exact ⟨List.prefix_refl _, id⟩

variable {I : ScalarInstance} {Q : Store Nat → Result → Prop}

/-- **Along a labelled run at a restricted universal host**, the functions and the tags are kept,
exceptions are only appended, and the tag invariants are kept. -/
theorem evRunQ_store {c c' : Config Nat} {cs : List (Call (wasmHostSig Nat))}
    (h : EvRun P (instHostQ I Q) c cs c') :
    c'.store.funcs = c.store.funcs ∧ c'.store.tags = c.store.tags ∧
      c.store.exns <+: c'.store.exns ∧ (TagsOk tags c.store → TagsOk tags c'.store) := by
  induction h with
  | refl => exact ⟨rfl, rfl, List.prefix_refl _, id⟩
  | silent hs _ ih =>
    rcases hs with hs | ⟨rfl, -⟩
    · obtain ⟨h₁, h₂, h₃, h₄⟩ := step_store (tags := tags) hs
      exact ⟨ih.1.trans h₁, ih.2.1.trans h₂, h₃.trans ih.2.2.1, fun hT => ih.2.2.2 (h₄ hT)⟩
    · exact ih
  | event hs _ ih =>
    obtain ⟨E, a, -, hs', h, rfl⟩ := hs
    rw [(Proofs.CfgInst.instHostQ_returned h).1] at ih
    exact ih

end Store

/-! ## 2. The relaxed domain -/

section Dom

variable {I : ScalarInstance}

theorem funcsWF_of_wf {s : Store Nat} (hw : I.WellFormed s) : FuncsWF I s :=
  ⟨hw.addrs_length, hw.export_type, hw.host_type⟩

theorem FuncsWF.congr {s s' : Store Nat} (hf : s'.funcs = s.funcs) (h : FuncsWF I s) :
    FuncsWF I s' := by
  refine ⟨h.addrs_length, fun j => ?_, fun a fi hh hfi hc => ?_⟩
  · rw [hf]; exact h.export_type j
  · rw [hf] at hfi; exact h.host_type a fi hh hfi hc

theorem importsTyped_of_funcsWF {s : Store Nat} (h : FuncsWF I s) : ImportsTyped I s := by
  intro hh fi hfi hcode
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hfi
  exact h.host_type a fi hh ha hcode

theorem invokeOk_of_funcsWF {s : Store Nat} (h : FuncsWF I s) (a : I.F.Op) :
    InvokeOk s (qOf I a).1 (qOf I a).2 := by
  obtain ⟨fi, hfi, hexp⟩ := h.export_type a.1
  refine ⟨fi, _, _, hfi, hexp, ?_⟩
  rw [Ty.toList_ofList]
  exact Proofs.Session.forall₂_valOk_of_hasVal s a.2.2

/-- A well-formed store in the checker's instruction profile is in the relaxed domain. -/
theorem instDomD_of_supported {s : Store Nat} (hw : I.WellFormed s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) : InstDomD I s :=
  ⟨funcsWF_of_wf hw, (instDom_of_supported hw hsup).chk,
    Abstract.TypedCatValid.exnsOk_of_storeOk hw.storeOk,
    DanglingTyped.storeOkD_of_storeOk hw.storeOk
      (DanglingTyped.funcsSupp_of_storeSupported hw.storeOk hsup)⟩

/-- The explicit domain with supported functions is in the relaxed domain. -/
theorem instDomD_of_instDom {s : Store Nat} (hd : InstDom I s) (hF : DanglingTyped.FuncsSupp s) :
    InstDomD I s :=
  ⟨funcsWF_of_wf hd.wf, hd.chk, Abstract.TypedCatValid.exnsOk_of_storeOk hd.wf.storeOk,
    DanglingTyped.storeOkD_of_storeOk hd.wf.storeOk hF⟩

/-- **Every export question of the relaxed domain enters `ConfigOkD`.** -/
theorem configOkD_of_domD {s : Store Nat} (hd : InstDomD I s) (a : I.F.Op) :
    DanglingTyped.ConfigOkD (invoke s (qOf I a).1 (qOf I a).2) := by
  obtain ⟨hF, hH, T, X, hg, hS⟩ := hd.okD
  have hw : FuncsWF I (DanglingTyped.gst s T X) :=
    ⟨hd.funcs.addrs_length, hd.funcs.export_type, hd.funcs.host_type⟩
  exact DanglingTyped.configOkD_invoke hF hH hg hS (invokeOk_of_funcsWF hw a)

/-- The tag of a real exception is a tag of the store, by `ExnsOk` at the real tags. -/
theorem tag_lt_of_exnsOk {s : Store Nat} (hx : Interp.ExnsOk s.tags s) {a : Nat} {e : ExnInst}
    (he : s.exns[a]? = some e) : e.tag < s.tags.length := by
  by_contra hlt
  have hn : s.tags[e.tag]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hlt)
  have h := hx a e he { tags := [e.tag] } ⟨0⟩ rfl
  simp only [Interp.tagFields] at h
  rw [show ([e.tag] : List Nat)[(⟨0⟩ : TagIdx).toNat]? = some e.tag from rfl] at h
  simp [hn] at h

/-- **The real exceptions of the relaxed domain are typed up to exception addresses**: the tag of
an exception instance of `s` is a tag `ti` of `s` (its real tags), of parameter types `ts`, and
its fields are, up to exception addresses, values of the types `ts` on the witness. -/
theorem exn_typed {s : Store Nat} (hd : InstDomD I s) {a : Nat} {e : ExnInst}
    (he : s.exns[a]? = some e) :
    ∃ (T : List TagInst) (X : List ExnInst) (ti : TagInst) (ts : Ty (.list .val))
      (fs : List Val), DanglingTyped.GhostOk s T X ∧ s.tags[e.tag]? = some ti ∧
      Expand ti.type (.func ts .nil) ∧ List.Forall₂ (DanglingTyped.ValApprox X.length) e.fields fs ∧
      List.Forall₂ (ValOk (DanglingTyped.gst s T X)) fs ts.toList := by
  obtain ⟨-, -, T, X, hg, hS⟩ := hd.okD
  obtain ⟨e', he', htag, hf⟩ := hg.real a e he
  obtain ⟨ti, ts, hti, hexp, hvs⟩ := hS.exns e' (List.mem_of_getElem? he')
  have hlt := tag_lt_of_exnsOk hd.exns he
  have hti' : s.tags[e.tag]? = some ti := by
    obtain ⟨u, hu⟩ := hg.tags
    rw [← hti, htag, ← hu, List.getElem?_append_left hlt]
  exact ⟨T, X, ti, ts, e'.fields, hg, hti', hexp, hf, hvs⟩

/-- **A labelled run of an export question of the relaxed domain at the unrestricted host ends in
the relaxed domain, with the same functions.** -/
theorem domD_of_evRun {P : Numerics.Profile} {s : Store Nat} (hd : InstDomD I s) (a : I.F.Op)
    {cs : List (Call (wasmHostSig Nat))} {c : Config Nat}
    (h : EvRun P (instHostU I) (invoke s (qOf I a).1 (qOf I a).2) cs c) :
    InstDomD I c.store ∧ c.store.funcs = s.funcs := by
  obtain ⟨hf, ht, -, hT⟩ := evRunQ_store (tags := s.tags) h
  change c.store.funcs = s.funcs at hf
  change c.store.tags = s.tags at ht
  have hc := DanglingTyped.ConfigOkD.evRun DanglingTyped.hostTypedD_instHostU
    (configOkD_of_domD hd a) h
  refine ⟨⟨FuncsWF.congr hf hd.funcs, ?_, ?_, DanglingTyped.storeOkD_of_configOkD hc⟩, hf⟩
  · rw [hf, ht]; exact hd.chk
  · rw [ht]; exact (hT ⟨rfl, hd.exns⟩).2

/-- **A finished round of the instance triple from the relaxed domain ends in the relaxed
domain, with the same functions** (every profile; traps that keep their store included). -/
theorem domD_of_round {P : Numerics.Profile} {s s₁ : Store Nat} (hd : InstDomD I s)
    {a : I.F.Op} {c : List (Call I.E)} {b : Abstract.InstSession.Res I.exports ⊕ PUnit}
    (hm : (c, .ret b s₁) ∈ (instTripleS I P).1 s a) : InstDomD I s₁ ∧ s₁.funcs = s.funcs := by
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple] at hm
  obtain ⟨⟨cs, e⟩, ⟨-, hy⟩, -, hv⟩ := hm
  obtain ⟨b', rfl⟩ := Proofs.CfgInst.viewEnd_ret hv
  have hI := importsTyped_of_funcsWF hd.funcs
  rcases b' with (ws | t) | u
  · exact domD_of_evRun hd a (Proofs.CfgInst.evRun_to_Q hy hI fun _ _ => trivial)
  · exact domD_of_evRun hd a (Proofs.CfgInst.evRun_to_Q hy hI fun _ _ => trivial)
  · exact domD_of_evRun hd a (Proofs.CfgInst.evRun_to_Q hy hI fun _ _ => trivial)

/-- **The relaxed domain persists along the instance session.** -/
theorem domD_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDomD I s₀)
    (hr : Reach (instTripleS I P) s₀ s) : InstDomD I s := by
  induction hr with
  | refl => exact hd
  | step hm _ ih => exact ih (domD_of_round hd hm).1

/-- **The instance session keeps the store's functions**, from the relaxed domain. -/
theorem funcs_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDomD I s₀)
    (hr : Reach (instTripleS I P) s₀ s) : s.funcs = s₀.funcs := by
  induction hr with
  | refl => rfl
  | step hm _ ih => exact (ih (domD_of_round hd hm).1).trans (domD_of_round hd hm).2

end Dom

/-! ## 3. Per question on the relaxed domain -/

section Agree

variable {I : ScalarInstance} {o : GrowOracle}

/-- **Every instance behaviour is a CFG behaviour at the unrestricted host**, on the relaxed
domain, at a deterministic profile. -/
theorem sub_cfgInstTripleU {s : Store Nat} (hd : InstDomD I s) (a : I.F.Op) :
    (instTripleS I (profile o)).1 s a ⊆ (cfgInstTripleU I).1 s a ∧
      (instTripleS I (profile o)).2.1 s a ⊆ (cfgInstTripleU I).2.1 s a ∧
      (instTripleS I (profile o)).2.2 s a ⊆ (cfgInstTripleU I).2.2 s a := by
  have hS := hd.chk
  have hts : TagsOk s.tags s := ⟨rfl, hd.exns⟩
  have hok := invokeOk_of_funcsWF hd.funcs a
  have hct := configOkD_of_domD hd a
  have hI := importsTyped_of_funcsWF hd.funcs
  have hT : (backD (H := Nat)).HostOk (instHostU I) := DanglingTyped.hostTypedD_instHostU
  have hH : Interp.HostSliceT (instHostU I) := Proofs.CfgInst.hostSliceT_instHostQ
  have hE : Interp.HostSliceE s.tags (instHostU I) := Proofs.CfgInst.hostSliceE_instHostQ _
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple]
  unfold cfgInstTripleU
  rw [CfgClosure.cfgSessionTripleC_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨y, ⟨-, hy⟩, hv⟩
    have hyU : CoreBehSXP (profile o) (instHostU I) s (qOf I a) y :=
      (Proofs.CfgInst.coreBehSXP_Q_iff (Q := fun _ _ => True) hI).2 ⟨hy, fun _ _ => trivial⟩
    exact ⟨y, ⟨backD.coreBehSXP_mem hT hH hE hct hS hts hok hyU,
      Proofs.DanglingBack.coreBehSXP_consistent hyU⟩, hv⟩
  · rintro x ⟨y, hy, hv⟩
    have hyU : CoreCallout (profile o) (instHostU I) s (qOf I a) y :=
      (Proofs.CfgInst.coreCallout_Q_iff (Q := fun _ _ => True) hI).2 ⟨hy, fun _ _ => trivial⟩
    obtain ⟨c, E, a', hrun, -, -⟩ := id hyU
    exact ⟨y, ⟨backD.coreCallout_mem hT hH hE hct hS hts hok hyU,
      Abstract.evRun_consistent hrun⟩, hv⟩
  · rintro ω ⟨ω', ⟨-, hω⟩, hv⟩
    have hωU : Abstract.CoreInf (profile o) (instHostU I) (invoke s (qOf I a).1 (qOf I a).2) ω' :=
      (Proofs.CfgInst.coreInf_Q_iff (Q := fun _ _ => True) hI).2 ⟨hω, fun _ => trivial⟩
    exact ⟨ω', ⟨backD.coreInf_mem hT hH hE hct hS hts hok hωU,
      fun n => Abstract.coreInf_consistent hωU n⟩, hv⟩

/-- **Every CFG instance behaviour at the unrestricted host is an instance behaviour**, on the
relaxed domain, at every profile. -/
theorem cfgInstTripleU_sub {P : Numerics.Profile} {s : Store Nat} (hd : InstDomD I s)
    (a : I.F.Op) :
    (cfgInstTripleU I).1 s a ⊆ (instTripleS I P).1 s a ∧
      (cfgInstTripleU I).2.1 s a ⊆ (instTripleS I P).2.1 s a ∧
      (cfgInstTripleU I).2.2 s a ⊆ (instTripleS I P).2.2 s a := by
  have hS := hd.chk
  have hts : TagsOk s.tags s := ⟨rfl, hd.exns⟩
  have hok := invokeOk_of_funcsWF hd.funcs a
  have hI := importsTyped_of_funcsWF hd.funcs
  have hH := Proofs.DanglingExn.hostSliceT_instHostU (I := I)
  have hE := Proofs.DanglingExn.hostSliceE_instHostU (I := I) s.tags
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple]
  unfold cfgInstTripleU
  rw [CfgClosure.cfgSessionTripleC_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨y, hy, hv⟩
    have h := Proofs.DanglingExn.fin_sub_of (P := P) hH hE hS hts hok hy
    exact ⟨y, ⟨trivial, ((Proofs.CfgInst.coreBehSXP_Q_iff (Q := fun _ _ => True) hI).1 h.2).1⟩,
      hv⟩
  · rintro x ⟨y, hy, hv⟩
    have h := Proofs.DanglingExn.pend_sub_of (P := P) hH hE hS hts hok hy
    exact ⟨y, ((Proofs.CfgInst.coreCallout_Q_iff (Q := fun _ _ => True) hI).1 h).1, hv⟩
  · rintro ω ⟨ω', hω, hv⟩
    have h := Proofs.DanglingExn.inf_sub_of (P := P) hH hE hS hts hok hω
    exact ⟨ω', ⟨trivial, ((Proofs.CfgInst.coreInf_Q_iff (Q := fun _ _ => True) hI).1 h.2).1⟩,
      hv⟩

/-- **Per question on the relaxed domain, the instance triple is the CFG instance triple at the
unrestricted host.** -/
theorem agree {s : Store Nat} (hd : InstDomD I s) (a : I.F.Op) :
    AgreeAt (instTripleS I (profile o)) (cfgInstTripleU I) s a := by
  obtain ⟨b₁, b₂, b₃⟩ := sub_cfgInstTripleU (o := o) hd a
  obtain ⟨f₁, f₂, f₃⟩ := cfgInstTripleU_sub (P := profile o) hd a
  exact ⟨Set.Subset.antisymm b₁ f₁, Set.Subset.antisymm b₂ f₂, Set.Subset.antisymm b₃ f₃⟩

end Agree

/-! ## 4. Sessions -/

section Session

variable {I : ScalarInstance} {o : GrowOracle}

/-- **The instance session is the CFG session at the unrestricted host**, from the relaxed
domain: every store reached by the session (`Reach`, finished returning or store-keeping trap
rounds) is in the domain (`domD_of_reach`), where the two triples agree at every question. -/
theorem threadS_eq {s₀ : Store Nat} (hd : InstDomD I s₀) :
    StratSession.threadS (instTripleS I (profile o)) s₀ =
      StratSession.threadS (cfgInstTripleU I) s₀ :=
  Proofs.CfgInst.threadS_eq_of_agree fun _ hr a => agree (domD_of_reach hd hr) a

theorem instSession_eq {s₀ : Store Nat} (hd : InstDomD I s₀) :
    instSession I (profile o) s₀ = cfgInstSessionU I s₀ :=
  threadS_eq hd

end Session

/-! ## 5. The raw domain is not kept: `ExampleAlias` -/

section Alias

open Silmaril.Wasm.Cfg.ExampleAlias

/-- The export question `run()` of `alI`. -/
abbrev alQ : alI.F.Op := ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩

/-- The import call `h()` of `alI` answered by the dangling exception `0`. -/
abbrev alCall : Call alI.E := ⟨⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩, Answer.throw 0⟩

theorem qOf_alQ : qOf alI alQ = (1, []) := by
  show (alI.addrs.getD 0 0, []) = (1, [])
  rw [show alI.addrs = [1] from Proofs.ExampleAlias.al_addrs]
  rfl

/-- **`run()` of `alI`, with `h()` answered by the dangling exception `0`, is a finished round of
the instance triple from `alStore` ending in `alEnd`** (every profile). -/
theorem al_round {P : Numerics.Profile} :
    ([alCall], .ret (.inl ⟨alQ, .inr 0⟩) alEnd) ∈ (instTripleS alI P).1 alStore alQ := by
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple]
  refine ⟨([alAns], .ret (.inl (.inr 0)) alEnd), ⟨trivial, ?_⟩, .cons ⟨?_, rfl, rfl⟩ .nil, rfl⟩
  · rw [qOf_alQ]
    exact (Proofs.CfgInst.evRun_of_Q ExampleAlias.run_core_U).1
  · simp [ScalarInstance.importOp?, ifaceOp?, alI]

theorem reach_alEnd {P : Numerics.Profile} : Reach (instTripleS alI P) alStore alEnd :=
  .step al_round (.refl _)

theorem not_instDom_alEnd : ¬ InstDom alI alEnd := fun h =>
  ExampleAlias.alEnd_not_storeOk h.wf.storeOk

theorem instDomD_alStore : InstDomD alI alStore :=
  instDomD_of_supported Proofs.ExampleAlias.al_wf ExampleAlias.al_supported

theorem instDomD_alEnd : InstDomD alI alEnd :=
  domD_of_reach (P := profile SingleThreaded.neverFail) instDomD_alStore reach_alEnd

end Alias

end Silmaril.Wasm.Cfg.Proofs.DanglingSession
