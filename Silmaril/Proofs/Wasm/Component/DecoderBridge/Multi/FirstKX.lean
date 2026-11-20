module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.NodesX
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.FirstK2

/-!
# The first node with its node end and the invariant (`FirstKX`)

`firstKX : FirstKX`: `Multi.FirstK2.firstK'` from the IR's node end (`NodeEnd`) rather than its
calls: the machine's core store after the first core instantiation is the IR's store after the
start function (host code renamed), so the first core instance is at the identity gap
(`nodeAt_gap0`); the frame relates to the reading with the component store (`FrameRelX`):

* `refFold_preX`: the reading of the definitions before the first core instantiation appends
  the resolved function types, keeps the component functions and exports, and its core functions
  and inline core instances only hold adapted functions;
* `frameRelX_root`: `frameRel_root` with the types, core functions, component functions, inline
  instances and exports of `FrameRelX`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
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
open Silmaril.Wasm.SingleThreaded (GrowOracle Internal status neverFail profile)

local notation "Σh" => Unit × List HLinked2.HostEvent

/-! ## The reading before the first core instantiation -/

section Read

theorem inline_mem {cf : List Impl} :
    ∀ {items : List (String × Syntax.SortIdx Syntax.CoreSort)} {es : List (String × Impl)},
      items.mapM (fun (p : String × Syntax.SortIdx Syntax.CoreSort) =>
        if p.2.sort = .func then (cf[p.2.idx]?).map ((p.1, ·)) else none) = some es →
      ∀ q ∈ es, q.2 ∈ cf
  | [], es, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | p :: items, es, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, es', hes', rfl⟩ := h
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · split at hx
      · obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
        exact List.mem_of_getElem? hy
      · cases hx
    · exact inline_mem hes' q hq

/-- Every core function and every function of an inline core instance is adapted. -/
def Adapted (R : RSt) : Prop :=
  (∀ im ∈ R.coreFuncs, im.chain ≠ []) ∧
    ∀ (k : Nat) its, R.coreInsts[k]? = some (RCI.inline its) → ∀ q ∈ its, q.2.chain ≠ []

/-- **The reading of the definitions before the first core instantiation** (without imports):
the function types appended, read from `synTypes`; the component functions and exports kept;
adapted core functions and inline instances. -/
theorem refFold_preX :
    ∀ (pre : List (Syntax.Definition Silmaril.Wasm.Module)) (nf ncf : Nat) (R R' : RSt),
      preOk nf ncf pre = true → noImport pre = true → pre.foldlM refStep R = some R' →
      Adapted R →
      (∃ X, R'.types = R.types ++ X ∧
        List.Forall₂ (fun f ft => refFuncTy f = some ft) (synTypes pre) X) ∧
      R'.funcs = R.funcs ∧ R'.exports = R.exports ∧ Adapted R'
  | [], _, _, R, R', _, _, h, hA => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨⟨[], by simp, by simp [synTypes]⟩, rfl, rfl, hA⟩
  | d :: ds, nf, ncf, R, R', hp, hni, h, hA => by
    have hni' : noImport ds = true := by
      simp only [noImport, List.all_cons, Bool.and_eq_true] at hni
      exact hni.2
    simp only [List.foldlM_cons] at h
    cases hR : refStep R d with
    | none => rw [hR] at h; cases h
    | some R₁ =>
    rw [hR] at h
    match d, hp, hR with
    | .coreModule mo, hp, hR =>
      simp only [refStep, Option.some.injEq] at hR
      subst hR
      obtain ⟨⟨X, h1, h2⟩, h3, h4, h5⟩ := refFold_preX ds nf ncf _ R' hp hni' h hA
      exact ⟨⟨X, h1, by simpa [synTypes] using h2⟩, h3, h4, h5⟩
    | .type (.func ft), hp, hR =>
      simp only [preOk, Bool.and_eq_true] at hp
      simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hR
      obtain ⟨ft', hft', rfl⟩ := hR
      obtain ⟨⟨X, h1, h2⟩, h3, h4, h5⟩ := refFold_preX ds nf ncf _ R' hp.2 hni' h hA
      exact ⟨⟨ft' :: X, by simp [h1], by simpa [synTypes] using (List.Forall₂.cons hft' h2 :
        List.Forall₂ (fun f ft => refFuncTy f = some ft) (ft :: synTypes ds) (ft' :: X))⟩,
        h3, h4, h5⟩
    | .canon (.lower g []), hp, hR =>
      simp only [preOk, Bool.and_eq_true, decide_eq_true_eq] at hp
      simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
      obtain ⟨⟨im, ft⟩, -, hR⟩ := hR
      split at hR
      · cases hR
      · simp only [Option.some.injEq] at hR
        subst hR
        have hA₁ : Adapted { R with coreFuncs := R.coreFuncs ++ [⟨.lower ft :: im.chain, im.target⟩] } := by
          refine ⟨fun im' him => ?_, hA.2⟩
          rcases List.mem_append.mp him with him | him
          · exact hA.1 im' him
          · simp only [List.mem_singleton] at him
            subst him
            simp
        obtain ⟨⟨X, h1, h2⟩, h3, h4, h5⟩ := refFold_preX ds nf (ncf + 1) _ R' hp.2 hni' h hA₁
        exact ⟨⟨X, h1, by simpa [synTypes] using h2⟩, h3, h4, h5⟩
    | .coreInstance (.exports items), hp, hR =>
      simp only [preOk, Bool.and_eq_true] at hp
      simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hR
      obtain ⟨es, hes, rfl⟩ := hR
      have hA₁ : Adapted { R with coreInsts := R.coreInsts ++ [.inline es] } := by
        refine ⟨hA.1, fun k its hk q hq => ?_⟩
        by_cases hlt : k < R.coreInsts.length
        · rw [List.getElem?_append_left hlt] at hk
          exact hA.2 k its hk q hq
        · rw [List.getElem?_append_right (Nat.not_lt.mp hlt)] at hk
          have hk' : k - R.coreInsts.length = 0 := by
            rcases Nat.eq_zero_or_pos (k - R.coreInsts.length) with h0 | h0
            · exact h0
            · rw [List.getElem?_eq_none (by simp; omega)] at hk
              cases hk
          rw [hk'] at hk
          simp only [List.getElem?_singleton, ite_true, Option.some.injEq, RCI.inline.injEq] at hk
          subst hk
          exact hA.1 _ (inline_mem hes q hq)
      obtain ⟨⟨X, h1, h2⟩, h3, h4, h5⟩ := refFold_preX ds nf ncf _ R' hp.2 hni' h hA₁
      exact ⟨⟨X, h1, by simpa [synTypes] using h2⟩, h3, h4, h5⟩
    | .import_ n (.func t), _, _ => simp [noImport] at hni

theorem forall₂_of_len {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length → (∀ a ∈ l₁, ∀ b, P a b) →
      List.Forall₂ P l₁ l₂
  | [], [], _, _ => .nil
  | a :: l₁, b :: l₂, hl, h =>
    .cons (h a List.mem_cons_self b)
      (forall₂_of_len (by simpa using hl) fun a' ha' b' => h a' (List.mem_cons_of_mem _ ha') b')
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem forall₂_zip {α β γ : Type} {P : α → β → Prop} {Q : α → γ → Prop} :
    ∀ {fs : List α} {X : List β} {ts : List γ}, List.Forall₂ P fs X → List.Forall₂ Q fs ts →
      List.Forall₂ (fun b c => ∃ a, P a b ∧ Q a c) X ts
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ r₁, .cons h₂ r₂ => .cons ⟨_, h₁, h₂⟩ (forall₂_zip r₁ r₂)

/-- **`frameRel_root` with `FrameRelX`**, for any component store. -/
theorem frameRelX_root {pre : RefComponent} {k : Nat} {R : RSt} {sc : Scope (core3 neverFail)}
    (S : CStore (core3 neverFail))
    (hshape : rootShape pre = true) (hpre : preOk 0 0 pre = true)
    (hR : pre.foldlM refStep ({ env := k } : RSt) = some R)
    (hty : sc.frame.types.length = nTypes pre) (htf : ∀ x ∈ sc.frame.types, ∃ t, x = .func t)
    (hfn : sc.frame.funcs.length = 1) (hcf : sc.frame.coreFuncs = List.range (preLowers pre))
    (hci : sc.frame.coreInstances = instsVal (preInsts pre)) (hex : sc.exports = [])
    (hT : List.Forall₂ TyEntry (synTypes pre) sc.frame.types) :
    FrameRelX (coreMods pre) R sc S ∧ Adapted R := by
  have hF := frameRel_root hshape hpre hR hty htf hfn hcf hci
  obtain ⟨pre', rfl, hni⟩ := rootShape_inv hshape
  have hpre' : preOk 1 0 pre' = true := by
    simp only [preOk, Bool.and_eq_true] at hpre
    exact hpre.2
  simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at hR
  obtain ⟨R₁, h₁, R₂, h₂, hR⟩ := hR
  simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₁
  obtain ⟨ft, hft, rfl⟩ := h₁
  simp only [refStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h₂
  obtain ⟨ft', -, rfl⟩ := h₂
  obtain ⟨⟨X, h1, h2⟩, h3, h4, hA⟩ := refFold_preX pre' 1 0 _ R hpre' hni hR
    ⟨by simp, fun k its hk => by simp at hk⟩
  have hT' : List.Forall₂ TyEntry (fFuncType :: synTypes pre') sc.frame.types := by
    simpa [synTypes] using hT
  refine ⟨⟨hF, ?_, ?_, ?_, hA.2, ?_⟩, hA⟩
  · rw [h1]
    have hP : List.Forall₂ (fun f ft => refFuncTy f = some ft) (fFuncType :: synTypes pre')
        ([ft] ++ X) := .cons hft h2
    simp only [List.nil_append] at hP ⊢
    exact (forall₂_zip hP hT').imp fun {ft x} ⟨f, hf, hfx, fr, t, ht, hx⟩ =>
      ⟨t, hx, f, fr, hfx, hf, ht⟩
  · refine forall₂_of_len hF.cf_len.symm fun im him a e he => ?_
    have := hA.1 im him
    rw [he] at this
    exact absurd rfl this
  · refine forall₂_of_len hF.funcs_len.symm fun x hx fid ft e he => ?_
    rw [h3] at hx
    simp only [List.nil_append, List.mem_singleton] at hx
    subst hx
    simp at he
  · rw [h4, hex]
    exact .nil

end Read
/-- **The first node, with its node end and the invariant.** -/
theorem firstKX : FirstKX := by
  intro b c r p ps x pre mi cargs post hc hr hf himp hn hu hq hs
  obtain ⟨t₀, J, mi₂, xs⟩ := x
  obtain ⟨hfi, hw, -, pre₁, mi₁, cargs₁, post₁, hs₁, hshape, hpostOk⟩ := multiImpFrag_inv hf
  rw [hs] at hs₁
  obtain ⟨rfl, rfl, rfl, rfl⟩ : pre = pre₁ ∧ mi = mi₁ ∧ cargs = cargs₁ ∧ post = post₁ := by
    simp only [Option.some.injEq, Prod.mk.injEq] at hs₁
    exact ⟨hs₁.1, hs₁.2.1, hs₁.2.2.1, hs₁.2.2.2⟩
  have hpostNI := noImport_of_postOk hpostOk
  obtain ⟨pre', post', mi', cargs', m, hs', hpre, hm, hlen, hlow, hrt, hmod, himps, hilen, hwl, hw',
    hnames⟩ := firstImp_setup hc hr hw hfi himp hn
  rw [hs] at hs'
  simp only [Option.some.injEq, Prod.mk.injEq] at hs'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs'
  obtain ⟨-, hp, ys, hF, hstart⟩ := hq
  dsimp only at hp hF hstart hu ⊢
  obtain ⟨hlog, hans⟩ := coreLog_eq hw' hwl hF hu
  rw [hmod, hilen] at hp
  -- the root, up to the first core instantiation
  obtain ⟨sc', Kr, hF', hKF, hfm, hcfs, hfi', htyl, htyf, hfnl, hex', hT'⟩ :=
    root_firstK2 hs hpre hshape hpostNI
  obtain ⟨tr₁, hob₁, d₁⟩ := hF' (fun _ => pure .unit) [] [] rfl
  generalize hK : (fun b => Kr b >>= fun _ => pure Ret.unit) = K at d₁
  have hKF' : KFin K := hK ▸ hKF
  let M₁ : Machine.Config (core3 neverFail) Σh := lowCfg hostConfigX (preLowers pre) lowH
  have hcore : M₁.store.core = lowStore m.imports.length lowH := by
    show lowStore (preLowers pre) lowH = _
    rw [hlen]
  have hmd : sc'.frame.coreModule? mi = some m := by
    simp only [Frame.coreModule?, hfm]
    exact hm
  have hci := coreImportsFor_low (o := neverFail) (h := lowH) (md := m) hfi' hlow hrt
  rw [← hcore] at hci
  cases hv : Silmaril.Wasm.Validation.validate? m with
  | none =>
    exfalso
    unfold Core3.prepareE? at hp
    rw [hv] at hp
    cases hp
  | some mt =>
  rw [importTypesE_length hv] at hci
  have hsh := prepareE_mapH (fun _ : Nat => lowH) (irStore m.imports.length) m
    ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
  rw [mapH_irStore, ← hcore] at hsh
  have hpr : (core3 neverFail).prepare? M₁.store.core m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
      some (Store.mapH gL J.store, mi₂, J.start) :=
    hsh.trans (by rw [hp]; rfl)
  have hready : HostReadyCfg hostConfigX := ⟨rfl, rfl, rfl⟩
  -- the frame after the first core instantiation and the symbolic reading
  have hFR : ∀ (S : CStore (core3 neverFail)) R₀,
      (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
      ({ env := (r.filter isFuncImport).length } : RSt) = some R₀ →
      FrameRelX (coreMods pre) R₀ ({ sc' with frame := { sc'.frame with
        coreInstances := sc'.frame.coreInstances ++ [(core3 neverFail).exports mi₂] } } :
          Scope (core3 neverFail)) S := by
    intro S R₀ hR₀
    rw [List.foldlM_append] at hR₀
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, List.foldlM_cons, List.foldlM_nil]
      at hR₀
    obtain ⟨R, hR, hR'⟩ := hR₀
    have hR'' : refStep R (.coreInstance (.instantiate mi cargs)) = some R₀ := by
      simpa using hR'
    exact frameRelX_inst (frameRelX_root S hshape hpre hR htyl htyf hfnl hcfs hfi' hex' hT').1
      hR'' hm rfl rfl rfl rfl rfl (prepareE?_exportsS hpr) ⟨[], by simp⟩
  -- the typing of the core store after the preparation, and its trampolines
  have hsOk₀ : Silmaril.Wasm.Execution.Core.StoreOk
      (Store.mapH gL (irStore m.imports.length)) := by
    rw [mapH_irStore]
    exact storeOk_lowStore _ _
  have hp₀ := prepareE_mapH gL (irStore m.imports.length) m
    ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
  rw [hp] at hp₀
  obtain ⟨hsJ, -, ⟨newJ, hnewJ, hwasmJ⟩, -⟩ :=
    Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hsOk₀ hp₀
  have hHT : HostTy (Store.mapH gL J.store) := by
    intro fi hfi h hcode
    rw [hnewJ, mapH_irStore] at hfi
    rcases List.mem_append.mp hfi with hfi | hfi
    · simp only [lowStore, List.mem_replicate] at hfi
      rw [hfi.2]
      rfl
    · obtain ⟨c, hc⟩ := hwasmJ fi hfi
      rw [hc] at hcode
      cases hcode
  have htramp : ∀ i, i < preLowers pre →
      (Store.mapH gL J.store).funcs[i]? = some (lowFI lowH) := by
    intro i hi
    rw [hnewJ, mapH_irStore, List.getElem?_append_left (by simp [lowStore]; omega)]
    simp [lowStore, show i < m.imports.length by omega]
  -- the program at the first core instantiation
  have hX : (List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc'
      (Syntax.Definition.coreInstance (.instantiate mi cargs) :: post) >>= K) =
      (instantiateCore ⟨0⟩ sc'.frame mi cargs >>= fun es =>
        (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc post >>= K) := by
    erw [List.foldlM_cons]
    simp only [instantiateDef, bind_assoc]
  erw [hX] at d₁
  -- the core instance on the frame, then the definitions after it
  have hpush : ∀ (es : List (String × (core3 neverFail).ExternVal)) (m₂ : Machine.Config (core3 neverFail) Σh),
      RunsQ (DG embL.host) none (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
        pure ({ sc' with frame := f } : Scope (core3 neverFail))) m₂ []
        ({ sc' with frame := { sc'.frame with coreInstances := sc'.frame.coreInstances ++ [es] } } :
          Scope (core3 neverFail)) m₂ := by
    intro es m₂
    simp only [pushEntry, need, orTrap, Frame.push, pure_bind]
    exact .pure _ _
  -- the final configuration is at the definitions after the first core instantiation
  have finish : ∀ (tr : List (Label (core3 neverFail) Σh)) (M : Machine.Config (core3 neverFail) Σh)
      (sc : Scope (core3 neverFail)),
      LRun first.prof embL.hr (DG embL.host)
        { hostConfigX with ctl := ⟨none, .prog (instantiateProg r (importArgs hostI) >>=
          fun _ => pure .unit), []⟩ :: [] } tr
        { M with ctl := ⟨none, .prog (List.foldlM (instantiateDef callRecurse ⟨0⟩ []
          (importArgs hostI)) sc post >>= K), []⟩ :: [] } → traceObs tr = [] →
      M.store.lockdown = false → M.host = ((), logOfCalls t₀) → LaterInv pre sc M →
      M.pending = [] → M.results = [] →
      (∃ es₀, sc.frame.coreInstances = instsVal (preInsts pre) ++ [es₀] ∧
        NodeAt M.store.core ⟨t₀, J, mi₂, xs⟩ es₀) →
      (∀ R₀, (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
        ({ env := (r.filter isFuncImport).length } : RSt) = some R₀ →
        FrameRelX (coreMods pre) R₀ sc M.store) →
      ∃ sc M, RefAtDefsK r post sc (logOfCalls t₀) M ∧ LaterInv pre sc M ∧
        M.pending = [] ∧ M.results = [] ∧
        (∃ tr, Steps first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX
          (.host (instantiateTop r (importArgs hostI)) :: tr) M ∧ (∀ ev, Label.host ev ∉ tr) ∧
          traceObs tr = []) ∧
        (∃ es₀, sc.frame.coreInstances = instsVal (preInsts pre) ++ [es₀] ∧
          NodeAt M.store.core ⟨t₀, J, mi₂, xs⟩ es₀) ∧
        ∀ R₀, (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
          ({ env := (r.filter isFuncImport).length } : RSt) = some R₀ →
          FrameRelX (coreMods pre) R₀ sc M.store := by
    intro tr M sc d hob hl hh hinv hpd hrs hes hfr
    refine ⟨sc, _, ⟨⟨tr, d, Adequacy.LRun.no_host d,
      fun msg => Adequacy.LRun.no_trap d ⟨List.cons_ne_nil _ _, hl⟩ _⟩, ⟨K, hKF', rfl⟩, hl, hh⟩,
      ?_⟩
    exact ⟨⟨hinv.mods, hinv.insts, hinv.lock, hinv.func0, hinv.inst, hinv.tramp, hinv.ok,
      hinv.hosts, hinv.depth⟩, hpd, hrs, ⟨tr, .cons (.hostRun hready) d.steps, Adequacy.LRun.no_host d, hob⟩,
      hes, hfr⟩
  rcases hstart with ⟨hnone, rfl, rfl⟩ | ⟨f, c', fvs, hfs, hrun, hst, rfl⟩
  · -- no start function
    have ht₀ : t₀ = [] := by cases hF; rfl
    subst ht₀
    rw [hnone] at hpr
    have hcore' : ∀ M : Machine.Config (core3 neverFail) Σh, M.store = M₁.store →
        RunsQ (DG embL.host) none (instantiateCore ⟨0⟩ sc'.frame mi cargs) M
        [.tau, .tau] ((core3 neverFail).exports mi₂)
        { M with store := setCoreSt (Store.mapH gL J.store) M.store } := by
      intro M hM
      unfold instantiateCore
      simp only [hmd, need, orTrap]
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      refine RunsQ.bind (tr₁ := [.tau]) (.get (.pure _ _)) ?_
      have hci' := hci
      have hpr' := hpr
      rw [← hM] at hci' hpr'
      rw [hci']
      refine RunsQ.bind (tr₁ := []) (.pure _ _) ?_
      erw [hpr']
      exact RunsQ.bind (tr₁ := [.tau])
        (.modify (f := setCoreSt (E := core3 neverFail) (Store.mapH gL J.store)) rfl (.pure _ _))
        (.pure _ _)
    have d₂ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) (RunsQ.bind (f := fun es =>
          pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
            pure ({ sc' with frame := f } : Scope (core3 neverFail))) (hcore' { M₁ with ctl :=
          ⟨none, .prog (instantiateCore ⟨0⟩ sc'.frame mi cargs >>= fun es =>
          (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
            pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
          List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
            (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K), []⟩ :: [] } rfl)
          (hpush _ _))
        (show M₁.store.lockdown = false from rfl)
        (fun sc => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
          (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K) (segs := []) (rest := [])
        (by simp only [bind_assoc])
    refine finish _ _ _ (d₁.trans d₂) (by
        simp only [traceObs] at hob₁ ⊢
        simp [List.filterMap_append, Label.obs?, hob₁]) rfl rfl ⟨by simpa using hfm,
      ⟨[(core3 neverFail).exports mi₂], by simp only [hfi']; rfl⟩, rfl,
      rfl, ⟨{}, rfl, .inl rfl⟩, htramp, hsJ, hHT, rfl⟩ rfl rfl
      ⟨_, by show sc'.frame.coreInstances ++ _ = _; rw [hfi']; rfl, nodeAt_gap0 rfl⟩ (hFR _)
  · -- a start function
    rw [hfs] at hpr
    have hrun' : Param.StartRunI (core3P (profile neverFail)) (CoreModule.imports p.1)
        (J.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) ys c' := hrun
    -- the core instantiation, up to its start call
    have hR : Reaches first.prof embL.hr (DG embL.host) none
        (Instantiate.runStart ⟨0⟩ f) (instantiateCore ⟨0⟩ sc'.frame mi cargs) M₁
        ([] ++ ([.tau] ++ ([] ++ ([.tau] ++ []))))
        { M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store }
        (fun m₂ tr' a m' => RunsQ (DG embL.host) none
          ((fun _ => pure ((core3 neverFail).exports mi₂)) ()) m₂ tr' a m') := by
      unfold instantiateCore
      simp only [hmd, need, orTrap]
      refine Reaches.seq (tr₁ := []) (.pure _ _) ?_
      refine Reaches.seq (tr₁ := [.tau]) (.get (.pure _ _)) ?_
      rw [hci]
      refine Reaches.seq (tr₁ := []) (.pure _ _) ?_
      erw [hpr]
      refine Reaches.seq (tr₁ := [.tau])
        (.modify (f := setCoreSt (E := core3 neverFail) (Store.mapH gL J.store)) rfl (.pure _ _)) ?_
      exact Reaches.here _ _
    obtain ⟨K', d₂, hK'⟩ := hR (fun es =>
        (pushEntry sc'.frame (.core .instance_) (.coreInstance es) >>= fun f =>
          pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
        List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
          (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K) [] [] rfl
    -- the start call, to the core activation
    obtain ⟨ι', hadd, hrem⟩ : ∃ ι', ({} : InstState).addThread? ⟨0⟩ = some (1, ι') ∧
        ι'.removeThread? 1 = some (⟨0⟩, InstState.removeThread 1 ι') := ⟨_, rfl, rfl⟩
    obtain ⟨M₀, thc, Kc, segsc, restc, tr₃, d₃, hob₃, hS⟩ := start_atG (impl := embL.host) first.prof
      { ({ M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store } :
          Machine.Config (core3 neverFail) Σh) with
        ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ f >>= K'), []⟩ :: [] }
      f {} ι' rfl rfl rfl hadd hrem
    have hml : ι'.mayLeave = true := by
      unfold InstState.addThread? at hadd
      obtain ⟨⟨i, tb⟩, -, he⟩ := Option.map_eq_some_iff.mp hadd
      cases he
      rfl
    have hB : CallInv M₀ thc := by
      have hth₀ := hS.thread
      subst hth₀
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hS.store]; rfl
      · rw [hS.store]; rfl
      · rw [hS.store]; exact ⟨ι', rfl, hml⟩
      · rw [hS.store]; rfl
    -- the typing of the start thread
    have hsOk : Silmaril.Wasm.Execution.Core.StoreOk (Store.mapH gL (irStore m.imports.length)) := by
      rw [mapH_irStore]
      exact storeOk_lowStore _ _
    have hp' := prepareE_mapH gL (irStore m.imports.length) m
      ((List.range m.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func)
    rw [hp, hfs] at hp'
    obtain ⟨hs', -, ⟨new, hnew, hwasm⟩, hcfg⟩ :=
      Silmaril.Wasm.Component.Engine.Core3.Typed.prepareE?_typed hsOk hp'
    have hRT : RT (Store.mapH gL J.store) (Silmaril.Wasm.SingleThreaded.Thread.invoke f []) := by
      refine ⟨hs', hcfg f rfl, fun fi hfi h hcode => ?_⟩
      rw [hnew, mapH_irStore] at hfi
      rcases List.mem_append.mp hfi with hfi | hfi
      · simp only [lowStore, List.mem_replicate] at hfi
        rw [hfi.2]
        rfl
      · obtain ⟨c, hc⟩ := hwasm fi hfi
        rw [hc] at hcode
        cases hcode
    have hM₀ : coreCfg M₀ thc Kc segsc restc
        (Store.mapH gL J.store, Silmaril.Wasm.SingleThreaded.Thread.invoke f []) = M₀ := by
      have e := coreCfg_self hS.ctl
      have hco : M₀.store.core = Store.mapH gL J.store := by rw [hS.store]; rfl
      rw [hco] at e
      exact e
    -- the start run with its host calls
    obtain ⟨tr₄, B', tR', d₄, hob₄, hst', hB', hhost, hExt, hRT'⟩ := startRun_refX (prof := first.prof)
      (K := Kc) (segs := segsc) (rest := restc) himps hrun' hans hst hB
      (tR := Silmaril.Wasm.SingleThreaded.Thread.invoke f []) rfl hRT
    rw [hM₀] at d₄
    -- no values
    have hfv : fvs = [] := by
      have := Silmaril.Wasm.Component.Engine.Core3.Typed.returned_typed (o := neverFail) (rs := [])
        ⟨hRT'.store, fun fi hfi h hc => ⟨_, hRT'.hosts fi hfi h hc⟩⟩ hRT'.thread hst'
      simpa using this
    subst hfv
    have d₅ := retStep (th := thc) (K := Kc) (segs := segsc) (rest := restc)
      (y := (Store.mapH gL c'.1, tR')) hst' hB'.lock
    -- the epilogue
    obtain ⟨h, xs, cs, rfl⟩ := hExt
    obtain ⟨tr₆, d₆, hob₆⟩ := hS.ret (Store.mapH gL c'.1, tR') h xs cs
    -- back in the core instantiation, then the core instance on the frame
    obtain ⟨d₇, -⟩ := hK' (startedCfgG embL.host { ({ M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store } :
          Machine.Config (core3 neverFail) Σh) with
          ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ f >>= K'), []⟩ :: [] }
          f ι' (Store.mapH gL c'.1) h xs cs) [] ((core3 neverFail).exports mi₂) _ (.pure _ _) rfl
    have d₈ := RunsQ.lrun_at (prof := first.prof) (hr := embL.hr) (hpush ((core3 neverFail).exports mi₂)
        { startedCfgG embL.host { ({ M₁ with store := setCoreSt (Store.mapH gL J.store) M₁.store } :
          Machine.Config (core3 neverFail) Σh) with
          ctl := ⟨none, .prog (Instantiate.runStart ⟨0⟩ f >>= K'), []⟩ :: [] }
          f ι' (Store.mapH gL c'.1) h xs cs with
          ctl := ⟨none, .prog ((pushEntry sc'.frame (.core .instance_)
            (.coreInstance ((core3 neverFail).exports mi₂)) >>= fun f =>
              pure ({ sc' with frame := f } : Scope (core3 neverFail))) >>= fun sc =>
            List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
              (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K), []⟩ :: [] })
      (show _ = false from rfl)
      (fun sc => List.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
        (post : List (Syntax.Definition (core3 neverFail).Module)) >>= K) (segs := []) (rest := [])
      rfl
    refine finish _ _ _ (d₁.trans (d₂.trans (d₃.trans (d₄.trans (d₅.trans (d₆.trans
      (d₇.trans d₈))))))) ?_ rfl ?_ ?_ rfl rfl
      ⟨_, by show sc'.frame.coreInstances ++ _ = _; rw [hfi']; rfl, nodeAt_gap0 rfl⟩ (hFR _)
    case refine_1 =>
      simp only [traceObs] at hob₁ hob₃ hob₄ hob₆ ⊢
      simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Label.obs?,
        hob₁, hob₃, hob₄, hob₆, List.nil_append, List.append_nil]
    case refine_3 =>
      have hfc : (Store.mapH gL c'.1).funcs = (Store.mapH gL J.store).funcs := by
        simp only [Store.mapH, startRunI_funcs hrun']
      refine ⟨by simpa using hfm, ⟨[(core3 neverFail).exports mi₂], by simp only [hfi']; rfl⟩, rfl, rfl,
        ⟨ι₁, by rw [← removeThread_ι₁ hadd]; rfl, .inr rfl⟩, fun i hi => ?_, hRT'.store,
        hRT'.hosts, rfl⟩
      show (Store.mapH gL c'.1).funcs[i]? = _
      rw [hfc]
      exact htramp i hi
    show h = _
    have hh : h = (M₀.host.1, M₀.host.2 ++ coreLog ys) := hhost
    rw [hh, hS.host, hlog]
    rfl

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
