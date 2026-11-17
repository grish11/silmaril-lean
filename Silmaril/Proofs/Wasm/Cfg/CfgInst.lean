module

public import Silmaril.Wasm.Cfg.CfgInst.Defs
public import Silmaril.Wasm.Cfg.CfgClosure.Thms
public import Silmaril.Wasm.Abstract.NodeBridge.Thms
public import Silmaril.Wasm.Abstract.HostSessionXP.Thms
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms
public import Silmaril.Wasm.Abstract.HostClosingS.Thms
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Abstract.TypedCatValid.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Wasm.SingleThreaded.Locality
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Proofs.Wasm.Cfg.Session

@[expose] public section

/-!
# Instance sessions built from the self-contained CFG closure (proofs)

See `Silmaril.Wasm.Cfg.CfgInst.Thms`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.CfgInst

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Cfg.CfgInst
open Silmaril.Wasm.Abstract (wasmHostSig coreHostRel HostTyped EvRun HEvStep CoreInf CoreBehSXP
  CoreObsLXP InvOkXP sessionTripleXP natTripleSXP)
open Silmaril.Wasm.Abstract.NodeBridge (instHost CallView qOf viewEnd viewTriple CoreCallout
  coreTripleSO)
open Silmaril.Wasm.Abstract.InstSession (Res sAns instTripleS instSession)
open Silmaril.Wasm.Interp (NativeHostSlice HostSliceT HostSliceE StoreChkE ehExt TagsOk)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Games.Abstract.StratThread (Reach)

/-! ## Host facts -/

section Host

variable {I : ScalarInstance}

theorem importOp?_fst {hh : Nat} {us : List Val} {e : I.E.Op} (h : I.importOp? hh us = some e) :
    e.1.1 = hh := by
  unfold ScalarInstance.importOp? ifaceOp? at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

theorem importOp?_self (e : I.E.Op) : I.importOp? e.1.1 e.2.1 = some e := by
  obtain ⟨⟨hh, hlt⟩, ⟨us, ht⟩⟩ := e
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · rfl
  · contradiction

/-- The results of an import, read from the type of a host function of a store where it is a
typed import. -/
theorem results_of_importTyped {s : Store Nat} {hh : Nat} {fi : FuncInst Nat}
    (hIT : ImportTyped I s hh) (hfi : fi ∈ s.funcs) (hcode : fi.code = .host hh)
    {e : I.E.Op} (he : e.1.1 = hh) {ps rs : Ty (.list .val)}
    (hexp : Expand fi.type (.func ps rs)) :
    rs.toList = (I.imports.get e.1).results.map ScalarType.toC := by
  obtain ⟨hlt, hx⟩ := hIT fi hfi hcode
  have hfe : e.1 = ⟨hh, hlt⟩ := Fin.ext he
  rw [hfe]
  have heq := Expand.func_eq hexp hx
  simp only [FnType.toComp, Ty.func.injEq] at heq
  rw [heq.2, Ty.toList_ofList]

theorem instHostNT_returned {hh : Nat} {s s' : Store Nat} {us : List Val} {r : Result}
    (h : instHostNT I hh s us (.returned s' r)) :
    s' = s ∧ ImportTyped I s hh ∧ NoThrow r ∧
      ∃ e, I.importOp? hh us = some e ∧ ∃ v : Answer (I.imports.get e.1), r = v.toResult := by
  obtain ⟨⟨e, he, v, hv⟩, hIT, hNT⟩ := h
  cases hv
  exact ⟨rfl, hIT, hNT _ _ rfl, e, he, v, rfl⟩

theorem not_instHostNT_diverged {hh : Nat} {s : Store Nat} {us : List Val} :
    ¬ instHostNT I hh s us .diverged :=
  fun h => Abstract.NodeBridge.not_instHost_diverged h.1

theorem storePreserving_instHostNT : Abstract.NodeBridge.StorePreserving (instHostNT I) :=
  fun _ _ _ _ _ h => (instHostNT_returned h).1

theorem hostTyped_instHostNT : HostTyped (instHostNT I) := by
  intro s fi hh vs ps rs hs hfi hcode hexp _ out hout
  cases out with
  | diverged => trivial
  | returned s' r =>
    obtain ⟨rfl, hIT, hNT, e, he, v, rfl⟩ := instHostNT_returned hout
    refine ⟨hs, Extend.refl hs, ?_⟩
    have hrs := results_of_importTyped hIT hfi hcode (importOp?_fst he) hexp
    cases v with
    | values ws =>
      show List.Forall₂ (ValOk _) ws.1 rs.toList
      rw [hrs]
      exact Proofs.Session.forall₂_valOk_of_hasVal _ ws.2
    | trap => trivial
    | throw t => exact (hNT t rfl).elim

theorem nativeHostSlice_instHostNT : NativeHostSlice (instHostNT I) where
  funcs _ _ _ _ _ h := by
    obtain ⟨rfl, -⟩ := instHostNT_returned h
    exact Interp.FuncsGood.refl _
  arity s a fi hh ps rs vs ws s' hfi hcode hty h := by
    obtain ⟨rfl, hIT, -, e, he, v, hv⟩ := instHostNT_returned h
    have hrs := results_of_importTyped hIT (List.mem_of_getElem? hfi) hcode (importOp?_fst he)
      (Proofs.Session.expand_of_funcType hty)
    rw [Ty.toList_ofList] at hrs
    cases v with
    | values w =>
      simp only [Answer.toResult, Result.values.injEq] at hv
      subst hv
      rw [hrs, List.length_map]
      exact w.2.length_eq.symm
    | trap => cases hv
    | throw t => cases hv
  noThrow _ _ _ _ t h := (instHostNT_returned h).2.2.1 t rfl

theorem hostSliceE_instHostNT (tags : List TagInst) : HostSliceE tags (instHostNT I) where
  chk _ _ _ _ _ h := by
    obtain ⟨rfl, -⟩ := instHostNT_returned h
    exact id
  tags _ _ _ _ _ h := by
    obtain ⟨rfl, -⟩ := instHostNT_returned h
    exact id

/-- **The obstruction**: as soon as the import signature has an operation, the universal host
answers it by an exception, so it is not in the native host slice. -/
theorem not_nativeHostSlice_instHost (e : I.E.Op) : ¬ NativeHostSlice (instHost I) := fun h =>
  h.noThrow e.1.1 I.store e.2.1 I.store 0 ⟨e, importOp?_self e, .throw 0, rfl⟩

theorem importsTyped_of_wf {s : Store Nat} (hw : I.WellFormed s) : ImportsTyped I s := by
  intro hh fi hfi hcode
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hfi
  exact hw.host_type a fi hh ha hcode

theorem importsTyped_congr {s s' : Store Nat} (hf : s'.funcs = s.funcs) (h : ImportsTyped I s) :
    ImportsTyped I s' := by
  intro hh fi hfi
  rw [hf] at hfi
  exact h hh fi hfi

end Host

/-! ## Runs under the universal host and under its non-throwing part -/

section Transfer

variable {I : ScalarInstance} {P : Numerics.Profile}

theorem hEvStep_none_iff {c c' : Config Nat} :
    HEvStep P (instHostNT I) c none c' ↔ HEvStep P (instHost I) c none c' := by
  constructor
  · rintro (h | ⟨-, E, a, hh, us, -, hd⟩)
    · exact .inl h
    · exact (not_instHostNT_diverged hd).elim
  · rintro (h | ⟨-, E, a, hh, us, -, hd⟩)
    · exact .inl h
    · exact (Abstract.NodeBridge.not_instHost_diverged hd).elim

theorem hEvStep_some_iff {c c' : Config Nat} {e : Call (wasmHostSig Nat)} :
    HEvStep P (instHostNT I) c (some e) c' ↔
      HEvStep P (instHost I) c (some e) c' ∧ ImportTyped I c.store e.1.1 ∧ NoThrow e.2.2 := by
  constructor
  · rintro ⟨E, a, hd, hs, ⟨h, hIT, hNT⟩, hc⟩
    exact ⟨⟨E, a, hd, hs, h, hc⟩, hIT, hNT _ _ rfl⟩
  · rintro ⟨⟨E, a, hd, hs, h, hc⟩, hIT, hNT⟩
    exact ⟨E, a, hd, hs, ⟨h, hIT, fun s' r heq => by cases heq; exact hNT⟩, hc⟩

theorem rtg_of_NT {c c' : Config Nat}
    (h : Relation.ReflTransGen (fun a b => HEvStep P (instHostNT I) a none b) c c') :
    Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hEvStep_none_iff.1 hs)

theorem rtg_to_NT {c c' : Config Nat}
    (h : Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) c c') :
    Relation.ReflTransGen (fun a b => HEvStep P (instHostNT I) a none b) c c' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hEvStep_none_iff.2 hs)

theorem hEvStep_funcs {c c' : Config Nat} {l : Option (Call (wasmHostSig Nat))}
    (h : HEvStep P (instHost I) c l c') : c'.store.funcs = c.store.funcs := by
  cases l with
  | none =>
    rcases h with h | ⟨rfl, -⟩
    · exact (SingleThreaded.Step.framesLocal h).1
    · rfl
  | some e =>
    obtain ⟨E, a, -, -, h, rfl⟩ := h
    show e.2.1.funcs = c.store.funcs
    rw [Abstract.NodeBridge.storePreserving_instHost _ _ _ _ _ h]

theorem rtg_none_funcs {c c' : Config Nat}
    (h : Relation.ReflTransGen (fun a b => HEvStep P (instHost I) a none b) c c') :
    c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (hEvStep_funcs hs).trans ih

theorem evRun_funcs {c c' : Config Nat} {cs : List (Call (wasmHostSig Nat))}
    (h : EvRun P (instHost I) c cs c') : c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | silent hs _ ih => exact ih.trans (hEvStep_funcs hs)
  | event hs _ ih => exact ih.trans (hEvStep_funcs hs)

theorem evRun_of_NT {c c' : Config Nat} {cs : List (Call (wasmHostSig Nat))}
    (h : EvRun P (instHostNT I) c cs c') :
    EvRun P (instHost I) c cs c' ∧ ∀ e ∈ cs, NoThrow e.2.2 := by
  induction h with
  | refl => exact ⟨.refl _, fun _ h => nomatch h⟩
  | silent hs _ ih => exact ⟨.silent (hEvStep_none_iff.1 hs) ih.1, ih.2⟩
  | event hs _ ih =>
    obtain ⟨hs', -, hN⟩ := hEvStep_some_iff.1 hs
    refine ⟨.event hs' ih.1, ?_⟩
    rintro e (_ | ⟨_, he⟩)
    · exact hN
    · exact ih.2 e he

theorem evRun_to_NT {c c' : Config Nat} {cs : List (Call (wasmHostSig Nat))}
    (h : EvRun P (instHost I) c cs c') :
    ImportsTyped I c.store → (∀ e ∈ cs, NoThrow e.2.2) → EvRun P (instHostNT I) c cs c' := by
  induction h with
  | refl => exact fun _ _ => .refl _
  | silent hs _ ih =>
    exact fun hI hN => .silent (hEvStep_none_iff.2 hs)
      (ih (importsTyped_congr (hEvStep_funcs hs) hI) hN)
  | @event c₁ _ _ e _ hs _ ih =>
    intro hI hN
    refine .event (hEvStep_some_iff.2 ⟨hs, ?_, hN e (.head _)⟩)
      (ih (importsTyped_congr (hEvStep_funcs hs) hI) fun e' he' => hN e' (.tail _ he'))
    obtain ⟨E, a, -, hs', -, -⟩ := hs
    exact hI _

/-- **Labelled runs at the non-throwing host are the throw-free runs at the universal host.** -/
theorem evRun_NT_iff {c c' : Config Nat} {cs : List (Call (wasmHostSig Nat))}
    (hI : ImportsTyped I c.store) :
    EvRun P (instHostNT I) c cs c' ↔ EvRun P (instHost I) c cs c' ∧ ∀ e ∈ cs, NoThrow e.2.2 :=
  ⟨evRun_of_NT, fun h => evRun_to_NT h.1 hI h.2⟩

theorem coreInf_NT_iff {c : Config Nat} {ω : Nat → Call (wasmHostSig Nat)}
    (hI : ImportsTyped I c.store) :
    CoreInf P (instHostNT I) c ω ↔ CoreInf P (instHost I) c ω ∧ ∀ k, NoThrow (ω k).2.2 := by
  constructor
  · rintro ⟨g, hg0, hg⟩
    refine ⟨⟨g, hg0, fun n => ?_⟩, fun k => ?_⟩
    · obtain ⟨c₁, hr, hs⟩ := hg n
      exact ⟨c₁, rtg_of_NT hr, (hEvStep_some_iff.1 hs).1⟩
    · obtain ⟨c₁, -, hs⟩ := hg k
      exact (hEvStep_some_iff.1 hs).2.2
  · rintro ⟨⟨g, hg0, hg⟩, hN⟩
    have hf : ∀ n, (g n).store.funcs = c.store.funcs := by
      intro n
      induction n with
      | zero => rw [hg0]
      | succ n ih =>
        obtain ⟨c₁, hr, hs⟩ := hg n
        rw [hEvStep_funcs hs, rtg_none_funcs hr, ih]
    refine ⟨g, hg0, fun n => ?_⟩
    obtain ⟨c₁, hr, hs⟩ := hg n
    refine ⟨c₁, rtg_to_NT hr, hEvStep_some_iff.2 ⟨hs, ?_, hN n⟩⟩
    exact importsTyped_congr ((rtg_none_funcs hr).trans (hf n)) hI _

theorem coreCallout_NT_iff {s : Store Nat} {q : Nat × List Val}
    {x : List (Call (wasmHostSig Nat)) × (wasmHostSig Nat).Op} (hI : ImportsTyped I s) :
    CoreCallout P (instHostNT I) s q x ↔
      CoreCallout P (instHost I) s q x ∧ ∀ e ∈ x.1, NoThrow e.2.2 := by
  constructor
  · rintro ⟨c, E, a', hr, hd, hs⟩
    obtain ⟨hr', hN⟩ := (evRun_NT_iff (c := invoke s q.1 q.2) hI).1 hr
    exact ⟨⟨c, E, a', hr', hd, hs⟩, hN⟩
  · rintro ⟨⟨c, E, a', hr, hd, hs⟩, hN⟩
    exact ⟨c, E, a', (evRun_NT_iff (c := invoke s q.1 q.2) hI).2 ⟨hr, hN⟩, hd, hs⟩

theorem coreBehSXP_NT_iff {s : Store Nat} {q : Nat × List Val}
    {y : CallBeh (wasmHostSig Nat) (Store Nat) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hI : ImportsTyped I s) :
    CoreBehSXP P (instHostNT I) s q y ↔
      CoreBehSXP P (instHost I) s q y ∧ ∀ e ∈ y.1, NoThrow e.2.2 := by
  have key := fun {c' : Config Nat} {cs : List (Call (wasmHostSig Nat))} =>
    evRun_NT_iff (P := P) (I := I) (c := invoke s q.1 q.2) (c' := c') (cs := cs) hI
  obtain ⟨cs, e⟩ := y
  cases e with
  | ret b s₂ =>
    rcases b with (ws | t) | u
    · exact key
    · exact key
    · exact key
  | trap => exact ⟨fun h => h.elim, fun h => h.1.elim⟩
  | div =>
    constructor
    · rintro ⟨c', hr, hd⟩
      obtain ⟨hr', hN⟩ := key.1 hr
      exact ⟨⟨c', hr', hd⟩, hN⟩
    · rintro ⟨⟨c', hr, hd⟩, hN⟩
      exact ⟨c', key.2 ⟨hr, hN⟩, hd⟩

end Transfer

/-! ## The view of throw-free logs -/

section View

variable {I : ScalarInstance}

theorem callView_noThrow {x : Call I.E} {ev : Call (wasmHostSig Nat)} (h : CallView I x ev) :
    NoThrowCall I x ↔ NoThrow ev.2.2 := by
  rw [h.2.2]
  obtain ⟨e, v⟩ := x
  cases v <;> simp [NoThrowCall, NoThrow, Answer.toResult]

theorem forall₂_noThrow {xs : List (Call I.E)} {ys : List (Call (wasmHostSig Nat))}
    (h : List.Forall₂ (CallView I) xs ys) :
    (∀ x ∈ xs, NoThrowCall I x) ↔ ∀ y ∈ ys, NoThrow y.2.2 := by
  induction h with
  | nil => simp
  | cons hxy _ ih => simp [callView_noThrow hxy, ih]

variable {P : Numerics.Profile}

/-- **Throw-free views of the universal host are the views of the non-throwing host**, at a store
whose host functions are typed imports (every profile). -/
theorem noThrowT_view_agree {s : Store Nat} (hI : ImportsTyped I s) (a : I.F.Op) :
    AgreeAt (noThrowT I (viewTriple I (coreTripleSO P (instHost I))))
      (viewTriple I (coreTripleSO P (instHostNT I))) s a := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨⟨y, ⟨-, hy⟩, hF, hv⟩, hN⟩
      exact ⟨y, ⟨trivial, (coreBehSXP_NT_iff hI).2 ⟨hy, (forall₂_noThrow hF).1 hN⟩⟩, hF, hv⟩
    · rintro ⟨y, ⟨-, hy⟩, hF, hv⟩
      obtain ⟨hy', hN⟩ := (coreBehSXP_NT_iff hI).1 hy
      exact ⟨⟨y, ⟨trivial, hy'⟩, hF, hv⟩, (forall₂_noThrow hF).2 hN⟩
  · ext x
    constructor
    · rintro ⟨⟨y, hy, hF, hv⟩, hN⟩
      exact ⟨y, (coreCallout_NT_iff hI).2 ⟨hy, (forall₂_noThrow hF).1 hN⟩, hF, hv⟩
    · rintro ⟨y, hy, hF, hv⟩
      obtain ⟨hy', hN⟩ := (coreCallout_NT_iff hI).1 hy
      exact ⟨⟨y, hy', hF, hv⟩, (forall₂_noThrow hF).2 hN⟩
  · ext ω
    constructor
    · rintro ⟨⟨ω', ⟨-, hω⟩, hv⟩, hN⟩
      exact ⟨ω', ⟨trivial, (coreInf_NT_iff hI).2 ⟨hω, fun k => (callView_noThrow (hv k)).1 (hN k)⟩⟩,
        hv⟩
    · rintro ⟨ω', ⟨-, hω⟩, hv⟩
      obtain ⟨hω', hN⟩ := (coreInf_NT_iff hI).1 hω
      exact ⟨⟨ω', ⟨trivial, hω'⟩, hv⟩, fun k => (callView_noThrow (hv k)).2 (hN k)⟩

end View

/-! ## The open Core triple is the openly restricted session triple -/

section Square

variable {H : Type} {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}

theorem coreTripleSO_fin_eq (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {q : Nat × List Val} (hok : InvOkXP tags s q) :
    (coreTripleSO (profile o) host).1 s q =
      (openRestrict (coreHostRel host) sessionTripleXP).1 s q := by
  ext x
  have h := Abstract.natTripleSXP_mem_iff (o := o) hT hH hE (s := s) (q := q) (x := x)
  constructor
  · intro hx
    have h' := h.2 ⟨hok, hx.2⟩
    exact ⟨h'.1.2, h'.2⟩
  · intro hx
    exact ⟨trivial, (h.1 ⟨⟨hok, hx.1⟩, hx.2⟩).2⟩

theorem coreTripleSO_pend_eq (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {q : Nat × List Val} (hok : InvOkXP tags s q) :
    (coreTripleSO (profile o) host).2.1 s q =
      (openRestrict (coreHostRel host) sessionTripleXP).2.1 s q := by
  ext ⟨cs, hh, s', us⟩
  obtain ⟨a, vs⟩ := q
  show CoreCallout (profile o) host s (a, vs) (cs, (hh, s', us)) ↔
    (cs, (hh, s', us)) ∈ Abstract.wasmEvPendXPS s (a, vs) ∧ (coreHostRel host).Consistent cs
  rw [Abstract.wasmEvPendXPS_eq]
  exact (Abstract.wasmEvPendXP_evRun_iff hT hH hE hok.1 hok.2.1 hok.2.2.1 hok.2.2.2).symm

theorem coreTripleSO_inf_eq (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {q : Nat × List Val} (hok : InvOkXP tags s q) :
    (coreTripleSO (profile o) host).2.2 s q =
      (openRestrict (coreHostRel host) sessionTripleXP).2.2 s q := by
  ext ω
  have h := Abstract.natTripleSXP_inf_iff (o := o) hT hH hE (s := s) (q := q) (ω := ω)
  constructor
  · intro hx
    have h' := h.2 ⟨hok, hx.2⟩
    exact ⟨h'.1.2, h'.2⟩
  · intro hx
    exact ⟨trivial, (h.1 ⟨⟨hok, hx.1⟩, hx.2⟩).2⟩

/-- **Per question, the open Core triple is the self-contained CFG session triple, openly
restricted by the host.** -/
theorem coreTripleSO_agree_cfg (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) {s : Store H} {q : Nat × List Val} (hok : InvOkXP tags s q) :
    AgreeAt (coreTripleSO (profile o) host)
      (openRestrict (coreHostRel host) CfgClosure.cfgSessionTripleC) s q := by
  rw [CfgClosure.cfgSessionTripleC_eq]
  exact ⟨coreTripleSO_fin_eq hT hH hE hok, coreTripleSO_pend_eq hT hH hE hok,
    coreTripleSO_inf_eq hT hH hE hok⟩

end Square

/-! ## The instance -/

section Inst

variable {I : ScalarInstance} {o : GrowOracle}

theorem invokeOk_of_wf {s : Store Nat} (hw : I.WellFormed s) (a : I.F.Op) :
    InvokeOk s (qOf I a).1 (qOf I a).2 := by
  obtain ⟨fi, hfi, hexp⟩ := hw.export_type a.1
  refine ⟨fi, _, _, hfi, hexp, ?_⟩
  rw [Ty.toList_ofList]
  exact Proofs.Session.forall₂_valOk_of_hasVal s a.2.2

theorem invOkXP_of_dom {s : Store Nat} (hd : InstDom I s) (a : I.F.Op) :
    InvOkXP s.tags s (qOf I a) :=
  ⟨hd.wf.storeOk, hd.chk, Abstract.TypedCatValid.tagsOk_of_storeOk hd.wf.storeOk,
    invokeOk_of_wf hd.wf a⟩

theorem viewTriple_agree {t t' : ObsTriple (wasmHostSig Nat) (Store Nat) (Nat × List Val)
    ((List Val ⊕ Nat) ⊕ PUnit)} {s : Store Nat} {a : I.F.Op} (h : AgreeAt t t' s (qOf I a)) :
    AgreeAt (viewTriple I t) (viewTriple I t') s a := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [viewTriple, h₁, h₂, h₃]

theorem agreeAt_trans {E : Sig.{0}} {S A B : Type} {t₁ t₂ t₃ : ObsTriple E S A B} {s : S} {a : A}
    (h₁ : AgreeAt t₁ t₂ s a) (h₂ : AgreeAt t₂ t₃ s a) : AgreeAt t₁ t₃ s a :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

/-- **The main per-question theorem**: on the domain, the throw-free instance triple and the CFG
instance triple agree. -/
theorem noThrowT_instTripleS_agree {s : Store Nat} (hd : InstDom I s) (a : I.F.Op) :
    AgreeAt (noThrowT I (instTripleS I (profile o))) (cfgInstTriple I) s a := by
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple]
  exact agreeAt_trans (noThrowT_view_agree (importsTyped_of_wf hd.wf) a)
    (viewTriple_agree (coreTripleSO_agree_cfg (o := o) hostTyped_instHostNT
      nativeHostSlice_instHostNT.toT (hostSliceE_instHostNT _) (invOkXP_of_dom hd a)))

/-! ## The domain persists -/

theorem step_tags_eq {H : Type} {P : Numerics.Profile} {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') : c'.store.tags = c.store.tags := by
  induction h with
  | «variable» h => cases h <;> rfl
  | table h => cases h <;> rfl
  | memory h => cases h <;> rfl
  | reference h => cases h <;> rfl
  | aggregate h => cases h <;> rfl
  | ctxtInstrs _ _ ih => exact ih
  | ctxtLabel _ ih => exact ih
  | ctxtHandler _ ih => exact ih
  | ctxtFrame _ ih => exact ih
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | _ => rfl

theorem evRun_NT_store {P : Numerics.Profile} {c c' : Config Nat}
    {cs : List (Call (wasmHostSig Nat))} (h : EvRun P (instHostNT I) c cs c') :
    c'.store.funcs = c.store.funcs ∧ c'.store.tags = c.store.tags := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | silent hs _ ih =>
    rcases hs with hs | ⟨rfl, -⟩
    · exact ⟨ih.1.trans (SingleThreaded.Step.framesLocal hs).1, ih.2.trans (step_tags_eq hs)⟩
    · exact ih
  | event hs _ ih =>
    obtain ⟨E, a, -, hs', h, rfl⟩ := hs
    rw [(instHostNT_returned h).1] at ih
    exact ih

theorem steps_configOk {P : Numerics.Profile} {c c' : Config Nat} {ts : List CValType}
    (h : Steps P (instHostNT I) c c') (hc : ConfigOk c ts) : ConfigOk c' ts := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact (Abstract.Step.preservation_typed hostTyped_instHostNT ih hs).1

/-- **A throw-free run of a typed invocation from the domain stays in the domain.** -/
theorem instDom_of_evRun {P : Numerics.Profile} {s : Store Nat} {q : Nat × List Val}
    {cs : List (Call (wasmHostSig Nat))} {c : Config Nat} (hd : InstDom I s)
    (hok : InvokeOk s q.1 q.2) (h : EvRun P (instHostNT I) (invoke s q.1 q.2) cs c) :
    InstDom I c.store := by
  obtain ⟨hf, ht⟩ := evRun_NT_store h
  obtain ⟨fi, ps, rs, -, -, hcfg⟩ := invoke_ok hd.wf.storeOk hok
  obtain ⟨C, ⟨hs, -⟩, -⟩ := steps_configOk (Abstract.evRun_steps h) hcfg
  change c.store.funcs = s.funcs at hf
  change c.store.tags = s.tags at ht
  refine ⟨⟨hs, hd.wf.addrs_length, fun j => ?_, fun a fi hh hfi hc => ?_⟩, ?_⟩
  · rw [hf]; exact hd.wf.export_type j
  · rw [hf] at hfi; exact hd.wf.host_type a fi hh hfi hc
  · rw [hf, ht]; exact hd.chk

theorem viewEnd_ret {a : I.F.Op} {e : End (Store Nat) ((List Val ⊕ Nat) ⊕ PUnit)}
    {b : Res I.exports ⊕ PUnit} {s₁ : Store Nat} (h : viewEnd I a e = some (.ret b s₁)) :
    ∃ b', e = .ret b' s₁ := by
  cases e with
  | ret b' s' =>
    simp only [viewEnd, Option.map_eq_some_iff, End.ret.injEq] at h
    obtain ⟨_, -, -, rfl⟩ := h
    exact ⟨b', rfl⟩
  | trap => simp [viewEnd] at h
  | div => simp [viewEnd] at h

/-- **A finished throw-free round from the domain ends in the domain.** -/
theorem instDom_of_round {P : Numerics.Profile} {s s₁ : Store Nat} (hd : InstDom I s)
    {a : I.F.Op} {c : List (Call I.E)} {b : Res I.exports ⊕ PUnit}
    (hm : (c, .ret b s₁) ∈ (noThrowT I (instTripleS I P)).1 s a) : InstDom I s₁ := by
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple] at hm
  rw [(noThrowT_view_agree (P := P) (importsTyped_of_wf hd.wf) a).1] at hm
  obtain ⟨⟨cs, e⟩, ⟨-, hy⟩, -, hv⟩ := hm
  obtain ⟨b', rfl⟩ := viewEnd_ret hv
  have hok := invokeOk_of_wf hd.wf a
  rcases b' with (ws | t) | u
  · exact instDom_of_evRun hd hok hy
  · exact instDom_of_evRun hd hok hy
  · exact instDom_of_evRun hd hok hy

theorem instDom_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDom I s₀)
    (hr : Reach (noThrowT I (instTripleS I P)) s₀ s) : InstDom I s := by
  induction hr with
  | refl => exact hd
  | step hm _ ih => exact ih (instDom_of_round hd hm)

/-- **A finished throw-free round from the domain keeps the store's functions.** -/
theorem funcs_of_round {P : Numerics.Profile} {s s₁ : Store Nat} (hd : InstDom I s)
    {a : I.F.Op} {c : List (Call I.E)} {b : Res I.exports ⊕ PUnit}
    (hm : (c, .ret b s₁) ∈ (noThrowT I (instTripleS I P)).1 s a) : s₁.funcs = s.funcs := by
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple] at hm
  rw [(noThrowT_view_agree (P := P) (importsTyped_of_wf hd.wf) a).1] at hm
  obtain ⟨⟨cs, e⟩, ⟨-, hy⟩, -, hv⟩ := hm
  obtain ⟨b', rfl⟩ := viewEnd_ret hv
  rcases b' with (ws | t) | u
  · exact (evRun_NT_store hy).1
  · exact (evRun_NT_store hy).1
  · exact (evRun_NT_store hy).1

/-- **The throw-free session keeps the store's functions**, from a store of the domain. -/
theorem funcs_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDom I s₀)
    (hr : Reach (noThrowT I (instTripleS I P)) s₀ s) : s.funcs = s₀.funcs := by
  induction hr with
  | refl => rfl
  | step hm _ ih => exact (ih (instDom_of_round hd hm)).trans (funcs_of_round hd hm)

/-! ## The session -/

theorem satP_congr {E : Sig.{0}} {S A B : Type} {t t' : ObsTriple E S A B} {s : S}
    (h₁ : t.1 s = t'.1 s) (h₂ : t.2.1 s = t'.2.1 s) (h₃ : t.2.2 s = t'.2.2 s) :
    satP t s = satP t' s := by
  funext a
  simp only [satP, h₁, h₂, h₃]

/-- **The throw-free instance session is the session of the CFG instance triple**, from a store
of the domain. -/
theorem threadS_noThrowT_eq {s₀ : Store Nat} (hd : InstDom I s₀) :
    StratSession.threadS (noThrowT I (instTripleS I (profile o))) s₀ =
      StratSession.threadS (cfgInstTriple I) s₀ := by
  refine StratSession.threadS_congr fun s hr => ?_
  have hd' := instDom_of_reach hd hr
  have h := fun a => noThrowT_instTripleS_agree (o := o) hd' a
  have h₁ : (noThrowT I (instTripleS I (profile o))).1 s = (cfgInstTriple I).1 s :=
    funext fun a => (h a).1
  have h₂ : (noThrowT I (instTripleS I (profile o))).2.1 s = (cfgInstTriple I).2.1 s :=
    funext fun a => (h a).2.1
  have h₃ : (noThrowT I (instTripleS I (profile o))).2.2 s = (cfgInstTriple I).2.2 s :=
    funext fun a => (h a).2.2
  exact ⟨h₁, satP_congr h₁ h₂ h₃, h₃⟩

/-- Without imports, no log or stream has a thrown answer: the restriction is the identity. -/
theorem noThrowT_eq_of_nil (h : I.imports = []) {S A B : Type} (t : ObsTriple I.E S A B) :
    noThrowT I t = t := by
  have hc := Proofs.Session.call_isEmpty h
  have hN : ∀ y : Call I.E, NoThrowCall I y := fun y => (hc.false y).elim
  obtain ⟨t₁, t₂, t₃⟩ := t
  simp only [noThrowT, hN, implies_true, and_true, Set.ofPred_mem_eq]

/-- **Without imports, the instance session is the session of the CFG instance triple**, from a
store of the domain. -/
theorem instSession_eq_cfg (h : I.imports = []) {s : Store Nat} (hd : InstDom I s) :
    instSession I (profile o) s = StratSession.threadS (cfgInstTriple I) s := by
  unfold instSession
  rw [← noThrowT_eq_of_nil h (instTripleS I (profile o))]
  exact threadS_noThrowT_eq hd

end Inst

/-- **`core3SemD` through CFG instance sessions** where they apply. -/
theorem core3SemD_eq_cfgInstSessions {o : GrowOracle} :
    Abstract.InstSession.core3SemD (profile o) =
      Abstract.InstSession.threadSemSD (cfgInstSessions o) := by
  unfold Abstract.InstSession.core3SemD
  congr 1
  funext m
  unfold cfgInstSessions
  split
  · next h => exact instSession_eq_cfg h.1 h.2
  · rfl

end Silmaril.Wasm.Cfg.Proofs.CfgInst
