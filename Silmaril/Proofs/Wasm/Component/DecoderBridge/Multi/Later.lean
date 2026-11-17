module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.First
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.IR

/-!
# The instantiation after the first node: the interface of its pieces

`Task.nodesRef` (the instantiation, pieces (b) and (c) together) is proved from three pieces,
whose statements are fixed here:

* `FirstK`: the first node, as `Task.firstNodeRef`, reaching the definitions after the first core
  instantiation at `RefAtDefsK` (the continuation of the definitions finishes the instantiation,
  `KFin`) with the machine invariant `LaterInv`;
* `LaterCoreStep`: a later core instantiation, from `LaterInv` and the IR node's `NodeCalls`, runs
  in the shared core store to the next definition with `LaterInv` again and the log of its calls;
  its core instance holds the module's exports;
* the definitions other than core instantiations, run silently, keep `LaterInv`
  (`LaterInv.congr`).

`LaterInv pre sc M`: the frame's core modules are those of `pre` and its core instances start with
the inline instances of `pre`; the store is not locked down, its component function `0` is the
root import `f`, its only component instance is fresh or has had one start thread (`InstOk`),
its core store starts with the trampolines of `pre`, is typed and its host functions have the core
type `fFlat`.
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

/-! ## The continuation of the definitions -/

/-- **The continuation finishes the instantiation**: from a configuration running `K sc`, the
machine runs by unique steps (`LRun`), without host events, to a configuration with the host in
control and the store not locked down, the same host state and core store, observing the instance
`0` with the function exports of `sc`. -/
def KFin (K : Scope (core3 neverFail) → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))) :
    Prop :=
  ∀ (sc : Scope (core3 neverFail)) (M : Machine.Config (core3 neverFail) Σh),
    M.store.lockdown = false → M.ctl = [.ofProg none (K sc)] →
    ∃ tr M', LRun first.prof embL.hr (DG embL.host) M tr M' ∧
      (∀ ev, Label.host ev ∉ tr) ∧ M'.ctl = [] ∧ M'.store.lockdown = false ∧
      M'.host = M.host ∧ M'.store.core = M.store.core ∧
      (traceObs tr).findSome? decodeInstantiated? = some (⟨0⟩, funcExports sc.exports)

/-- The configuration after the instantiation host event: the host frame runs the instantiation
program. -/
abbrev instCfg (r : RefComponent) : Machine.Config (core3 neverFail) Σh :=
  { hostConfigX with ctl := ⟨none, .prog (instantiateProg r (importArgs hostI) >>=
      fun _ => pure .unit), []⟩ :: [] }

/-- **The reference machine at the definitions `post`, with a finishing continuation**: reached
from the instantiation host event by unique steps (`LRun` from `instCfg r`), without host events
or internal faults; the continuation `K` of the definitions finishes the instantiation (`KFin`);
the store is not locked down and the host log is `L`. -/
def RefAtDefsK (r post : RefComponent) (sc : Scope (core3 neverFail))
    (L : List HLinked2.HostEvent) (M : Machine.Config (core3 neverFail) Σh) : Prop :=
  (∃ tr, LRun first.prof embL.hr (DG embL.host) (instCfg r) tr M ∧
    (∀ ev, Label.host ev ∉ tr) ∧ (∀ msg, Label.trap (.internal msg) ∉ tr)) ∧
  (∃ K, KFin K ∧
    M.ctl = [.ofProg none (post.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc
      >>= K)]) ∧
  M.store.lockdown = false ∧ M.host = ((), L)

/-! ## The machine invariant -/

/-- The component instance after one start thread: its thread table has slot `1` free. -/
def ι₁ : InstState := { threads := ⟨#[none, none], [1]⟩ }

/-- The only component instance is fresh, or has had one start thread. -/
def InstOk (ι : InstState) : Prop := ι = {} ∨ ι = ι₁

/-- **The machine invariant at the later definitions.** -/
structure LaterInv (pre : RefComponent) (sc : Scope (core3 neverFail))
    (M : Machine.Config (core3 neverFail) Σh) : Prop where
  mods : sc.frame.coreModules = coreMods pre
  insts : ∃ X : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr)),
    sc.frame.coreInstances = (instsVal (preInsts pre) ++ X :
      List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr)))
  lock : M.store.lockdown = false
  func0 : ArenaField.funcs.get? M.store ⟨0⟩ = some (.host fWit ⟨0⟩)
  inst : ∃ ι, M.store.insts = [ι] ∧ InstOk ι
  tramp : ∀ i, i < preLowers pre → M.store.core.funcs[i]? = some (lowFI lowH)
  ok : Silmaril.Wasm.Execution.Core.StoreOk M.store.core
  hosts : HostTy M.store.core

/-- **Definitions that only push frame entries and component functions keep the invariant.** -/
theorem LaterInv.congr {pre : RefComponent} {sc sc' : Scope (core3 neverFail)}
    {M M' : Machine.Config (core3 neverFail) Σh} (h : LaterInv pre sc M)
    (hm : sc'.frame.coreModules = sc.frame.coreModules)
    (hi : sc'.frame.coreInstances = sc.frame.coreInstances)
    {fs : List (CFuncInst (core3 neverFail))}
    (hs : M'.store = { M.store with funcs := M.store.funcs ++ fs }) : LaterInv pre sc' M' := by
  obtain ⟨hmods, hinsts, hlock, hf0, hinst, htr, hok, hh⟩ := h
  refine ⟨hm.trans hmods, hi ▸ hinsts, by rw [hs]; exact hlock, ?_, by rw [hs]; exact hinst,
    by rw [hs]; exact htr, by rw [hs]; exact hok, by rw [hs]; exact hh⟩
  rw [hs]
  have h0 : M.store.funcs[0]? = some (.host fWit ⟨0⟩) := hf0
  show (M.store.funcs ++ fs)[0]? = _
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h0).1, h0]

/-! ## The pieces -/

/-- **The first node, with a finishing continuation and the invariant**: `Task.firstNodeRef`,
reaching `RefAtDefsK` and `LaterInv`. -/
def FirstK : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (p : Binary.CoreMod × List Impl) (ps : List (Binary.CoreMod × List Impl))
    (t₀ : List (Σ _ : sigU.Op, Option Payload)) (pre : RefComponent) (mi : Nat)
    (cargs : List (String × Nat)) (post : RefComponent),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → MultiImpFrag r →
    c.imports = hostI → c.nodes = coreNodes (p :: ps) → (∀ x ∈ t₀, x.2 = InstTests.unitV) →
    NodeCalls hostI.length .ready p.1 p.2 t₀ →
    firstCore? r = some (pre, mi, cargs, post) →
    ∃ sc M, RefAtDefsK r post sc (logOfCalls t₀) M ∧ LaterInv pre sc M

/-- **A later core instantiation**: from the definitions `.coreInstance (.instantiate mi cargs) ::
ds` with the invariant, an IR node of the module `m` ready after the calls `t` (each answered
`()`), the machine runs live without host events, traps or observations to the definitions `ds`,
with the invariant, the log of the calls appended, and a new core instance holding the exports of
`m` (function exports as functions). -/
def LaterCoreStep : Prop :=
  ∀ (pre : RefComponent) (mi : Nat) (cargs : List (String × Nat)) (ds : RefComponent)
    (sc : Scope (core3 neverFail)) (M : Machine.Config (core3 neverFail) Σh)
    (m : Silmaril.Wasm.Module) (p : Binary.CoreMod × List Impl)
    (t : List (Σ _ : sigU.Op, Option Payload)) (L : List HLinked2.HostEvent)
    (K : Scope (core3 neverFail) → Canon.P (core3 neverFail) Σh (Ret (core3 neverFail))),
    (coreMods pre)[mi]? = some m →
    postDefOk (preLowers pre) (preInsts pre) (coreMods pre)
      (.coreInstance (.instantiate mi cargs)) = true →
    Binary.coreModule p.1 = m → (CoreModule.imports p.1).length = m.imports.length → NodeOk p →
    NodeCalls hostI.length .ready p.1 p.2 t →
    (∀ x ∈ t, x.2 = InstTests.unitV) →
    LaterInv pre sc M →
    M.ctl = [.ofProg none
      ((Syntax.Definition.coreInstance (.instantiate mi cargs) :: ds).foldlM
        (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc >>= K)] →
    M.host = ((), L) →
    ∃ (tr : List (Label (core3 neverFail) Σh)) (M' : Machine.Config (core3 neverFail) Σh)
      (sc' : Scope (core3 neverFail)) (es : List (String × (core3 neverFail).ExternVal)),
      LRun first.prof embL.hr (DG embL.host) M tr M' ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ msg, Label.trap msg ∉ tr) ∧
      M'.ctl = [.ofProg none
        (ds.foldlM (instantiateDef callRecurse ⟨0⟩ [] (importArgs hostI)) sc' >>= K)] ∧
      LaterInv pre sc' M' ∧ M'.host = ((), L ++ logOfCalls t) ∧
      sc'.frame.coreModules = sc.frame.coreModules ∧
      sc'.frame.coreInstances = sc.frame.coreInstances ++ [es] ∧
      sc'.frame.coreFuncs = sc.frame.coreFuncs ∧ sc'.exports = sc.exports ∧
      List.Forall₂ (fun (e : Silmaril.Wasm.Export) (x : String × (core3 neverFail).ExternVal) =>
        x.1 = e.name ∧ ∀ i, e.index = .func i → ∃ a : Nat, x.2 = Silmaril.Wasm.Execution.Core.ExternAddr.func a)
        m.exports es

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
