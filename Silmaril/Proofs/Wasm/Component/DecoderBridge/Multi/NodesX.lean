module

public import Silmaril.Wasm.Component.DecoderBridge.MultiX.Defs

/-!
# The instantiation with node ends and the invariant: the interface of its pieces

`NodesInv` (`MultiX.Defs`) is established by strengthening the pieces of `Multi.Nodes`:

* `FirstKX`: `FirstK'` for the IR's first node ending at `x` (`NodeEnd`), with the first core
  instance at `x` (`NodeAt`, the identity gap `gap0`), the frame related to the reading with the
  component store (`FrameRelX`), and no top-level calls;
* `LaterCoreStepX`: `LaterCoreStep'` for a later node ending at `x`, with the shared core store
  after it the gap image of `x.store` past the store before it, the core instance relocated, the
  component functions appended, and the top-level calls unchanged.

General facts: the store followed by more objects (`Store.app`, `nodeAt_app`), the identity gap
(`gap0_rel`, `gap0_minst`, `nodeAt_gap0`), and the relation `FrameRelX` kept by appending
(`envAddr_mono`, `funcRelS_mono`, `frameRelX_inst`).
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

/-! ## Stores followed by more objects -/

section App

variable {H : Type}

theorem store_app_assoc (a b c : Silmaril.Wasm.Execution.Core.Store H) :
    Store.app (Store.app a b) c = Store.app a (Store.app b c) := by
  simp [Store.app, List.append_assoc]

theorem store_app_nil (s : Silmaril.Wasm.Execution.Core.Store H) : Store.app s {} = s := by
  obtain ⟨⟩ := s
  simp [Store.app]

end App

theorem nodeAt_app {S : RStore} {x : NodeRun}
    {es : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)} (h : NodeAt S x es)
    (V : RStore) : NodeAt (Store.app S V) x es := by
  obtain ⟨g, hP, ⟨U, rfl⟩, he⟩ := h
  exact ⟨g, hP, ⟨Store.app U V, store_app_assoc _ _ _⟩, he⟩

/-! ## The identity gap -/

section Gap0

variable {H : Type}

/-- The gap of nothing: no store before, no import kept. -/
def gap0 : Gap H := ⟨{}, 0⟩

theorem gap0_fnMap (a : Nat) : (gap0 : Gap H).fnMap a = a := by
  simp [Gap.fnMap, gap0]

theorem gap0_ref : ∀ r : Silmaril.Wasm.Execution.Core.Ref, (gap0 : Gap H).sh.ref r = r
  | .struct a => by simp [GShift.ref, Gap.sh, gap0]
  | .array a => by simp [GShift.ref, Gap.sh, gap0]
  | .func a => by simp [GShift.ref, Gap.sh, gap0, Gap.fnMap]
  | .exn a => by simp [GShift.ref, Gap.sh, gap0]
  | .extern r => by simp only [GShift.ref]; rw [gap0_ref r]
  | .null => rfl
  | .i31 _ => rfl
  | .host _ => rfl

theorem gap0_val (v : Silmaril.Wasm.Execution.Core.Val) : (gap0 : Gap H).sh.val v = v := by
  cases v with
  | ref r => simp only [GShift.val, gap0_ref]
  | _ => rfl

theorem gap0_fval (v : Silmaril.Wasm.Execution.Core.FieldVal) : (gap0 : Gap H).sh.fval v = v := by
  cases v with
  | val v => simp only [GShift.fval, gap0_val]
  | _ => rfl

theorem gap0_xa (x : Silmaril.Wasm.Execution.Core.ExternAddr) : (gap0 : Gap H).sh.xa x = x := by
  cases x <;> simp [GShift.xa, Gap.sh, gap0, Gap.fnMap]

theorem gap0_minst (mi : Silmaril.Wasm.Execution.Core.ModuleInst) :
    (gap0 : Gap H).sh.minst mi = mi := by
  have hx : (gap0 : Gap H).sh.xinst = id := funext fun x => by
    simp [GShift.xinst, gap0_xa]
  have hf : (gap0 : Gap H).sh.fn = id := funext gap0_fnMap
  obtain ⟨⟩ := mi
  simp only [GShift.minst, hf, List.map_id, hx]
  simp [Gap.sh, gap0]

theorem gap0_store (t : Silmaril.Wasm.Execution.Core.Store H) : (gap0 : Gap H).sh.store t = t := by
  have hr : (gap0 : Gap H).sh.ref = id := funext gap0_ref
  have hv : (gap0 : Gap H).sh.val = id := funext gap0_val
  have hfv : (gap0 : Gap H).sh.fval = id := funext gap0_fval
  have hm : (gap0 : Gap H).sh.minst = id := funext gap0_minst
  have hg : (gap0 : Gap H).sh.ginst = id := funext fun g => by simp [GShift.ginst, hv]
  have ht : (gap0 : Gap H).sh.tinst = id := funext fun g => by simp [GShift.tinst, hr]
  have hf : ((gap0 : Gap H).sh.finst : Silmaril.Wasm.Execution.Core.FuncInst H → _) = id :=
    funext fun g => by simp [GShift.finst, hm]
  have he : (gap0 : Gap H).sh.einst = id := funext fun g => by simp [GShift.einst, hr]
  have hs : (gap0 : Gap H).sh.sinst = id := funext fun g => by simp [GShift.sinst, hfv]
  have ha : (gap0 : Gap H).sh.ainst = id := funext fun g => by simp [GShift.ainst, hfv]
  have hxn : (gap0 : Gap H).sh.xninst = id := funext fun g => by
    obtain ⟨tg, fs⟩ := g
    simp only [GShift.xninst, hv, List.map_id]
    simp [Gap.sh, gap0]
  obtain ⟨⟩ := t
  simp [GShift.store, hg, ht, hf, he, hs, ha, hxn]

theorem gap0_rel (t : Silmaril.Wasm.Execution.Core.Store H) : (gap0 : Gap H).rel t = t := by
  simp only [Gap.rel, gap0_store]
  obtain ⟨⟩ := t
  simp [Store.app, gap0]

theorem gap0_preOk (fs : List (Silmaril.Wasm.Execution.Core.FuncInst H)) : (gap0 : Gap H).PreOk fs :=
  ⟨Nat.zero_le _, fun a ha => absurd ha (Nat.not_lt_zero a)⟩

/-- **The first node**: the core store is the IR's, host code renamed. -/
theorem nodeAt_gap0 {S : RStore} {x : NodeRun}
    (h : S = Silmaril.Proofs.Wasm.Component.Reference.Store.mapH gL x.store) :
    NodeAt S x ((core3 neverFail).exports x.minst) :=
  ⟨gap0, gap0_preOk _, ⟨{}, by rw [store_app_nil, gap0_rel, h]⟩, by rw [gap0_minst]⟩

end Gap0

/-! ## The relation to the reading, kept by appending -/

section Mono

variable {R R' : RSt} {cis cis' : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr))}

theorem envAddr_mono {e a : Nat} (h : EnvAddr R cis e a)
    (hR : ∃ X, R'.coreInsts = R.coreInsts ++ X) (hc : ∃ Y, cis' = cis ++ Y) :
    EnvAddr R' cis' e a := by
  obtain ⟨k, base, i, exps, es, nm, ft, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨X, hX⟩ := hR
  obtain ⟨Y, rfl⟩ := hc
  refine ⟨k, base, i, exps, es, nm, ft, ?_, ?_, h3, h4, h5⟩
  · rw [hX, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1, h1]
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h2).1, h2]

theorem funcs_get_mono {S S' : CStore (core3 neverFail)} {fid : FuncId} {f : CFuncInst (core3 neverFail)}
    (h : ArenaField.funcs.get? S fid = some f) (hS : ∃ fs, S'.funcs = S.funcs ++ fs) :
    ArenaField.funcs.get? S' fid = some f := by
  obtain ⟨fs, hfs⟩ := hS
  have h' : S.funcs[fid.1]? = some f := h
  show S'.funcs[fid.1]? = some f
  rw [hfs, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h').1, h']

theorem funcRelS_mono {S S' : CStore (core3 neverFail)} {x : Impl × FuncTy} {fid : FuncId}
    (h : FuncRelS S R cis x fid) (hS : ∃ fs, S'.funcs = S.funcs ++ fs)
    (hR : ∃ X, R'.coreInsts = R.coreInsts ++ X) (hc : ∃ Y, cis' = cis ++ Y) :
    FuncRelS S' R' cis' x fid := by
  intro ft e hx
  obtain ⟨a, ty, h1, h2, h3, h4⟩ := h ft e hx
  exact ⟨a, ty, funcs_get_mono h1 hS, h2, envAddr_mono h3 hR hc, h4⟩

theorem forall₂_imp_mono {α β : Type} {P Q : α → β → Prop} (h : ∀ a b, P a b → Q a b)
    {l₁ : List α} {l₂ : List β} (hl : List.Forall₂ P l₁ l₂) : List.Forall₂ Q l₁ l₂ :=
  hl.imp fun {a b} => h a b

/-- **A core instantiation keeps the relation**: the reading pushes the node's core instance,
the frame the core instance `es`, the component store only appends component functions. -/
theorem frameRelX_inst {pre : RefComponent} {mi : Nat} {cargs : List (String × Nat)}
    {sc sc' : Scope (core3 neverFail)} {m : Silmaril.Wasm.Module}
    {es : List (String × (core3 neverFail).ExternVal)} {S S' : CStore (core3 neverFail)}
    (hF : FrameRelX (coreMods pre) R sc S)
    (hR : refStep R (.coreInstance (.instantiate mi cargs)) = some R')
    (hm : (coreMods pre)[mi]? = some m)
    (hci : sc'.frame.coreInstances = sc.frame.coreInstances ++ [es])
    (hcf : sc'.frame.coreFuncs = sc.frame.coreFuncs) (hty : sc'.frame.types = sc.frame.types)
    (hfn : sc'.frame.funcs = sc.frame.funcs) (hex : sc'.exports = sc.exports)
    (hE : List.Forall₂ (fun (e : Silmaril.Wasm.Export) (x : String × (core3 neverFail).ExternVal) =>
        x.1 = e.name ∧ ∀ i, e.index = .func i →
          ∃ a : Nat, x.2 = Silmaril.Wasm.Execution.Core.ExternAddr.func a) m.exports es)
    (hS : ∃ fs, S'.funcs = S.funcs ++ fs) :
    FrameRelX (coreMods pre) R' sc' S' := by
  obtain ⟨m', nm, imps, exps, w, -, -, -, hR1, hR2, hR3, hR4, hR5⟩ := refStep_inst hR
  have hRX : ∃ X, R'.coreInsts = R.coreInsts ++ X := ⟨_, hR1⟩
  have hcX : ∃ Y, sc'.frame.coreInstances = sc.frame.coreInstances ++ Y := ⟨_, hci⟩
  have hRexp : R'.exports = R.exports := by
    simp only [refStep, Option.bind_eq_some_iff, Option.some.injEq, bind] at hR
    obtain ⟨_, _, _, _, _, _, rfl⟩ := hR
    rfl
  refine ⟨frameRel_inst hF.rel hR hm hci hcf hty hfn hE, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR3, hty]; exact hF.types
  · rw [hR5, hcf]
    exact forall₂_imp_mono (fun im a h e he => envAddr_mono (h e he) hRX hcX) hF.coreFuncs
  · rw [hR4, hfn]
    exact forall₂_imp_mono (fun x fid h => funcRelS_mono h hS hRX hcX) hF.funcs
  · intro k its hk
    rw [hR1, List.getElem?_append] at hk
    split at hk
    · exact hF.inline k its hk
    · rw [List.getElem?_singleton] at hk
      split at hk <;> simp at hk
  · rw [hRexp, hex]
    exact forall₂_imp_mono (fun x y ⟨fid, h1, h2⟩ => ⟨fid, h1, funcRelS_mono h2 hS hRX hcX⟩)
      hF.exports

end Mono

/-- The relation does not depend on the component store beyond its functions. -/
theorem frameRelX_funcs {mods : List Silmaril.Wasm.Module} {R : RSt} {sc : Scope (core3 neverFail)}
    {S S' : CStore (core3 neverFail)} (h : FrameRelX mods R sc S) (hS : S'.funcs = S.funcs) :
    FrameRelX mods R sc S' := by
  have hS' : ∃ fs, S'.funcs = S.funcs ++ fs := ⟨[], by simp [hS]⟩
  have hX : ∃ X, R.coreInsts = R.coreInsts ++ X := ⟨[], by simp⟩
  have hY : ∃ Y, sc.frame.coreInstances = sc.frame.coreInstances ++ Y :=
    ⟨[], (List.append_nil _).symm⟩
  exact ⟨h.rel, h.types, h.coreFuncs,
    forall₂_imp_mono (fun x fid h => funcRelS_mono h hS' hX hY) h.funcs, h.inline,
    forall₂_imp_mono (fun x y ⟨fid, h1, h2⟩ => ⟨fid, h1, funcRelS_mono h2 hS' hX hY⟩) h.exports⟩

/-! ## The pieces, with node ends and the invariant -/

/-- **`FirstK'` with the node end and the invariant**: the first node ending at `x`; the first
core instance at `x` (`NodeAt`); the frame related to the reading with the component store; no
top-level calls; no observation so far. -/
def FirstKX : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (p : Binary.CoreMod × List Impl) (ps : List (Binary.CoreMod × List Impl)) (x : NodeRun)
    (pre : RefComponent) (mi : Nat) (cargs : List (String × Nat)) (post : RefComponent),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → MultiImpFrag r →
    c.imports = hostI → c.nodes = coreNodes (p :: ps) → (∀ y ∈ x.calls, y.2 = InstTests.unitV) →
    NodeEnd hostI.length p.1 p.2 x →
    firstCore? r = some (pre, mi, cargs, post) →
    ∃ sc M, RefAtDefsK r post sc (logOfCalls x.calls) M ∧ LaterInv pre sc M ∧
      M.pending = [] ∧ M.results = [] ∧
      (∃ tr, Steps first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX
        (.host (instantiateTop r (importArgs hostI)) :: tr) M ∧ (∀ ev, Label.host ev ∉ tr) ∧
        traceObs tr = []) ∧
      (∃ es₀, sc.frame.coreInstances = instsVal (preInsts pre) ++ [es₀] ∧
        NodeAt M.store.core x es₀) ∧
      ∀ R₀, (pre ++ [Syntax.Definition.coreInstance (.instantiate mi cargs)]).foldlM refStep
          ({ env := (r.filter isFuncImport).length } : RSt) = some R₀ →
        FrameRelX (coreMods pre) R₀ sc M.store

/-- **`LaterCoreStep'` with the node end**: the shared core store after the core instantiation is
the gap image of the IR's store after the start function, past the store before it, and the core
instance its module instance relocated; component functions are only appended; the top-level calls
are unchanged; nothing is observed. -/
def LaterCoreStepX : Prop :=
  ∀ (pre : RefComponent) (mi : Nat) (cargs : List (String × Nat)) (ds : RefComponent)
    (sc : Scope (core3 neverFail)) (M : Machine.Config (core3 neverFail) Σh)
    (m : Silmaril.Wasm.Module) (p : Binary.CoreMod × List Impl) (x : NodeRun)
    (L : List HLinked2.HostEvent)
    (K : Scope (core3 neverFail) → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))),
    (coreMods pre)[mi]? = some m →
    postDefOk (preLowers pre) (preInsts pre) (coreMods pre)
      (.coreInstance (.instantiate mi cargs)) = true →
    Binary.coreModule p.1 = m → (CoreModule.imports p.1).length = m.imports.length → NodeOk p →
    NodeEnd hostI.length p.1 p.2 x →
    (∀ y ∈ x.calls, y.2 = InstTests.unitV) →
    LaterInv pre sc M →
    M.ctl = [.ofProg none
      ((Syntax.Definition.coreInstance (.instantiate mi cargs) :: ds).foldlM
        (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc >>= K)] →
    M.host = ((), L) →
    ∃ (tr : List (Label (core3 neverFail) Σh)) (M' : Machine.Config (core3 neverFail) Σh)
      (sc' : Scope (core3 neverFail)) (g : Gap (CanonHost (core3 neverFail))),
      LRun first.prof embL.hr (DG embL.host) M tr M' ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ msg, Label.trap msg ∉ tr) ∧ traceObs tr = [] ∧
      M'.ctl = [.ofProg none
        (ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc' >>= K)] ∧
      LaterInv pre sc' M' ∧ M'.host = ((), L ++ logOfCalls x.calls) ∧
      sc'.frame.coreModules = sc.frame.coreModules ∧
      sc'.frame.coreInstances = sc.frame.coreInstances ++
        [(core3 neverFail).exports (g.sh.minst x.minst)] ∧
      sc'.frame.coreFuncs = sc.frame.coreFuncs ∧ sc'.exports = sc.exports ∧
      List.Forall₂ (fun (e : Silmaril.Wasm.Export) (y : String × (core3 neverFail).ExternVal) =>
        y.1 = e.name ∧ ∀ i, e.index = .func i → ∃ a : Nat, y.2 = Silmaril.Wasm.Execution.Core.ExternAddr.func a)
        m.exports ((core3 neverFail).exports (g.sh.minst x.minst)) ∧
      sc'.frame.types = sc.frame.types ∧ sc'.frame.funcs = sc.frame.funcs ∧
      g.pre = M.store.core ∧
      g.PreOk (Silmaril.Proofs.Wasm.Component.Reference.Store.mapH gL x.store).funcs ∧
      M'.store.core = g.rel (Silmaril.Proofs.Wasm.Component.Reference.Store.mapH gL x.store) ∧
      (∃ fs, M'.store.funcs = M.store.funcs ++ fs) ∧
      M'.pending = M.pending ∧ M'.results = M.results

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
