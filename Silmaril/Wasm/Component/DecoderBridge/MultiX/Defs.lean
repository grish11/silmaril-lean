module

public import Silmaril.Wasm.Component.DecoderBridge.Multi.Defs
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.Nodes
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.GapShift

/-!
# The instantiation on `MultiImpFrag` with its invariant, and the export call

`Multi.Defs` splits `Task.startAdequacyFrag` (the start goal on the fragment `MultiImpFrag`) into
the instantiation (`Task.nodesRef`, proved) and the export call (`Task.exportRef`). The latter
quantifies over an **arbitrary** finished instantiation `Instantiates … M inst es`, which says
nothing about the configuration `M` beyond its trace. Here the instantiation carries what the
export call needs.

**Scope.** This is the split fragment `MultiImpFrag` only: core instances whose imports are
`canon lower`ed functions of the component's imports, modules without memories, tables, tags,
data or element segments (no shared memory or table), and option-less `canon lift`s on flat
primitive types (no canonical-ABI memory, strings or lists). It is not an adequacy result for
general shared memory, tables or the canonical ABI.

## The IR's nodes, with their ends

* `NodeRun`: a ready node of the IR: its host calls, its engine instance before the start
  function (`Param.IInstance`), the module instance and the store the start function leaves.
* `NodeEnd n cm args x`: the engine instance of `cm` is `x.inst` (prepared against fresh host
  functions, `irStore`, with module instance `x.minst`), its start function (if any) runs with
  the import calls answered by the wiring `args` as one call each of the component's imports
  (`x.calls`) and returns, leaving `x.store`. `NodeCalls n .ready` is `∃ x, NodeEnd` with
  `x.calls` the calls (`Multi.Thms.nodeCalls_iff`).

## The reference machine after the instantiation

* `NodeAt S x es`: the shared core store `S` begins with the IR's store `x.store` (host code
  renamed to the trampolines) relocated along a gap `g` (`Gap.rel`: imports kept, the module's
  own objects past the store before it), followed by later objects `U`; the core instance `es`
  is the IR's module instance, relocated.
* `TyRel ty ft`, `EnvAddr R cis e a`, `FuncRelS`, `FrameRelX mods R sc S`: the frame `sc` and the
  component store `S` against the symbolic reading `R` (`refRead`): function types resolved from
  the same definitions; a core function wiring `Impl.fwd e` (export `e` of the environment) at
  the core address `a` of that export in the frame's core instance; a component function wiring
  `lift ft` of `Impl.fwd e` an option-less lifted function at that address; inline core instances
  exporting only adapted functions (the trampolines); the exports in order.
* **`NodesInv r ps xs M inst es`**: the instance is `0`; the host is in control, the store not
  locked down and at nesting depth `0` (the readiness of a host event), its component instance fresh or after one start thread, component function `0`
  the root import, no pending or resolved top-level calls; the core store is typed; the final
  frame relates to the reading of `r` (`FrameRelX`), its function exports are `es`, and its
  core instances after the inline ones are the nodes' (`NodeAt`, in order).

## The pieces

* `Task.nodesRefX` (proved: `MultiX.Thms.nodesRefX`): `Task.nodesRef` with explicit node ends
  and the invariant;
* `Task.exportRefX` (the export call, from the invariant at arbitrary node ends; open, and no
  longer on the path to the start goal);
* the start goal from three pieces (`MultiX.Thms.startAdequacyFrag_of_parts`): `Task.exportIR`
  (the IR's export phase: the play's node ends `xs`, at which the first export is the lift of a
  node export that runs without host calls to one `i32`, `ExportAt`; proved:
  `MultiX.Thms.exportIR`), `Task.coreRunShared` (that run in the shared core store; proved:
  `MultiX.Thms.coreRunShared`) and `Task.callLift` (the session call through `canon lift` around
  it; proved: `MultiX.Thms.callLift`). So `Task.startAdequacyFrag` is proved
  (`MultiX.Thms.startAdequacyFrag`).
-/

@[expose] public noncomputable section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.SingleThreaded (profile neverFail)
open Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi (Gap FrameRel InstOk)
open Silmaril.Proofs.Wasm.Component.DecoderBridge.FirstImp (gL irStore instsVal HostTy)
open Silmaril.Proofs.Wasm.Component.Reference (Store.app)

/-- The engine of the IR's core modules. -/
abbrev irEng : Engine := core3P (profile neverFail)

/-! ## The IR's nodes, with their ends -/

/-- **A ready node of the IR**: its calls to the component's imports, its engine instance before
the start function, the module instance and the store after the start function. -/
structure NodeRun where
  /-- The calls to the component's imports, each with its answer. -/
  calls : List (Σ _ : sigU.Op, Option Payload)
  /-- The engine instance before the start function. -/
  inst : Param.IInstance irEng
  /-- The module instance of the preparation. -/
  minst : Silmaril.Wasm.Execution.Core.ModuleInst
  /-- The store after the start function (`inst.store` without one). -/
  store : Silmaril.Wasm.Execution.Core.Store Nat

/-- **The IR's node `cm` (wired by `args` over `n` imports) is ready, ending at `x`**: its engine
instance is `x.inst`, prepared against fresh host functions with module instance `x.minst`; its
start function (if any) runs with the import calls `ys`, each answered by the wiring with one call
of `x.calls`, and returns values, leaving `x.store`. -/
def NodeEnd (n : Nat) (cm : Binary.CoreMod) (args : List Impl) (x : NodeRun) : Prop :=
  Param.instOfI irEng (Binary.coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) =
      some x.inst ∧
    Silmaril.Wasm.Component.Engine.Core3.prepareE? (irStore (CoreModule.imports cm).length)
        (Binary.coreModule cm)
        ((List.range (CoreModule.imports cm).length).map Silmaril.Wasm.Execution.Core.ExternAddr.func) =
      some (x.inst.store, x.minst, x.inst.start) ∧
    ∃ ys : List (Σ _ : (sigN (CoreModule.imports cm).length).Op, Option Payload),
      List.Forall₂ (fun y z => ∃ k, implsN n args (CoreModule.imports cm).length y.1 = .call z.1 k ∧
        k z.2 = .pure y.2) ys x.calls ∧
      ((x.inst.start = none ∧ ys = [] ∧ x.store = x.inst.store) ∨
        ∃ f c' vs, x.inst.start = some f ∧
          Param.StartRunI irEng (CoreModule.imports cm) (x.inst.store, irEng.invoke f []) ys c' ∧
          irEng.status c'.1 c'.2 = .returned (.values vs) ∧ x.store = c'.1)

/-! ## The reference machine after the instantiation -/

/-- The core store of the reference machine. -/
abbrev RStore : Type := Silmaril.Wasm.Execution.Core.Store (CanonHost (core3 neverFail))

/-- **Node `x` in the shared core store `S`, with the core instance `es`**: `S` begins with the
IR's store after the node's start function, host code renamed to the trampolines, relocated
along the gap `g` (its first `g.b` functions, the imports, kept; its own objects moved past
`g.pre`), followed by the objects `U` of later nodes; `es` is the IR's module instance,
relocated. -/
def NodeAt (S : RStore) (x : NodeRun) (es : List (String × Silmaril.Wasm.Execution.Core.ExternAddr)) :
    Prop :=
  ∃ g : Gap (CanonHost (core3 neverFail)),
    g.PreOk (Silmaril.Proofs.Wasm.Component.Reference.Store.mapH gL x.store).funcs ∧
    (∃ U : RStore, S = Store.app (g.rel (Silmaril.Proofs.Wasm.Component.Reference.Store.mapH gL x.store)) U) ∧
    es = (core3 neverFail).exports (g.sh.minst x.minst)

/-- **The reference function type `ty` and the IR's `ft` come from one definition**: a
primitive function type `f`, read by the IR as `ft` and resolved by the reference machine as
`ty`. -/
def TyRel (ty : Types.FuncType RtId) (ft : FuncTy) : Prop :=
  ∃ (f : Syntax.FuncType) (fr : Instantiate.Frame (core3 neverFail)),
    funcTypePrim f = true ∧ refFuncTy f = some ft ∧ Instantiate.resolveFuncType? fr f = some ty

/-- **Export `e` of the environment is the core function at `a`**: it is export `i` of the core
instance `k` of the reading (`.node base exps`, `e = base + i`), whose frame entry `es` maps its
name to the core function `a`. -/
def EnvAddr (R : RSt) (cis : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr)))
    (e a : Nat) : Prop :=
  ∃ (k base i : Nat) (exps : CoreIface) (es : List (String × Silmaril.Wasm.Execution.Core.ExternAddr))
    (nm : String) (ft : CoreFuncTy),
    R.coreInsts[k]? = some (.node base exps) ∧ cis[k]? = some es ∧ exps[i]? = some (nm, ft) ∧
    e = base + i ∧ es.lookup nm = some (.func a)

/-- **The component function `fid` of `S` and the reading's entry `x`**: if `x` is the lift of
type `ft` of export `e` of the environment, then `fid` is the option-less lift (instance `0`) of
the core function at `a` (`EnvAddr`), at a reference type related to `ft`. -/
def FuncRelS (S : CStore (core3 neverFail)) (R : RSt)
    (cis : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr))) (x : Impl × FuncTy)
    (fid : FuncId) : Prop :=
  ∀ ft e, x.1 = ⟨[.lift ft], .call e⟩ →
    ∃ a ty, ArenaField.funcs.get? S fid = some (.lifted a ty {} ⟨0⟩) ∧ TyRel ty ft ∧
      EnvAddr R cis e a ∧ x.2 = ft

/-- **The frame `sc` and the component store `S` against the reading `R`**: the index spaces
(`FrameRel`); the function types; the core functions forwarding an export of the environment;
the lifted component functions; the inline core instances, of adapted functions only; the
exports, in order. -/
structure FrameRelX (mods : List Silmaril.Wasm.Module) (R : RSt) (sc : Instantiate.Scope (core3 neverFail))
    (S : CStore (core3 neverFail)) : Prop where
  rel : FrameRel mods R sc
  types : List.Forall₂ (fun ft x => ∃ ty, x = Types.TypeDef.func ty ∧ TyRel ty ft) R.types
    sc.frame.types
  coreFuncs : List.Forall₂ (fun (im : Impl) (a : Nat) =>
    ∀ e, im = Impl.fwd e → EnvAddr R sc.frame.coreInstances e a) R.coreFuncs sc.frame.coreFuncs
  funcs : List.Forall₂ (FuncRelS S R sc.frame.coreInstances) R.funcs sc.frame.funcs
  inline : ∀ (k : Nat) its, R.coreInsts[k]? = some (RCI.inline its) → ∀ q ∈ its, q.2.chain ≠ []
  exports : List.Forall₂ (fun (x : Export) (y : String × Instantiate.ItemVal (core3 neverFail)) =>
    ∃ fid, y = (x.name, .func fid) ∧ FuncRelS S R sc.frame.coreInstances (x.impl, x.ty) fid)
    R.exports sc.exports

/-- **The reference machine after the instantiation of `r`, node by node**: instance `0`; the
host in control, no lockdown, nesting depth `0`, one component instance (fresh or after one start thread),
component function `0` the root import, no top-level calls; a typed core store whose host
functions are trampolines of type `fFlat`; the final frame `sc` related to the reading of `r`
(`FrameRelX`), its function exports `es`, its core instances the inline ones of the definitions
before the first core instantiation followed by the nodes' (`NodeAt`, in order). -/
structure NodesInv (r : RefComponent) (xs : List NodeRun)
    (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)) (inst : InstId)
    (es : List (String × FuncId)) : Prop where
  inst0 : inst = ⟨0⟩
  ctl : M.ctl = []
  lock : M.store.lockdown = false
  /-- The host's instantiation program has left its `nesting_depth += 1` bracket. -/
  depth : M.store.nestingDepth = 0
  insts : ∃ ι, M.store.insts = [ι] ∧ InstOk ι
  func0 : ArenaField.funcs.get? M.store ⟨0⟩ = some (.host fWit ⟨0⟩)
  calls : M.pending = [] ∧ M.results = []
  core : Silmaril.Wasm.Execution.Core.StoreOk M.store.core ∧ HostTy M.store.core
  frame : ∃ (R : RSt) (sc : Instantiate.Scope (core3 neverFail)) (pre : RefComponent) (mi : Nat)
      (cargs : List (String × Nat)) (post : RefComponent)
      (esN : List (List (String × Silmaril.Wasm.Execution.Core.ExternAddr))),
    refRead r = some R ∧ firstCore? r = some (pre, mi, cargs, post) ∧
    es = funcExports sc.exports ∧ FrameRelX (coreMods pre) R sc M.store ∧
    sc.frame.coreInstances = instsVal (preInsts pre) ++ esN ∧
    List.Forall₂ (NodeAt M.store.core) xs esN

/-! ## The pieces -/

/-- **The instantiation, with node ends and the invariant** (proved: `MultiX.Thms.nodesRefX`):
in the fragment, if the IR's nodes are ready ending at `xs`, each call answered `()`, the
reference machine finishes the instantiation with the host log of all the calls, and the final
configuration satisfies `NodesInv`. -/
def Task.nodesRefX : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (ps : List (Binary.CoreMod × List Impl)) (xs : List NodeRun),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → MultiImpFrag r →
    c.imports = hostI → c.nodes = coreNodes ps →
    (∀ x ∈ (xs.map NodeRun.calls).flatten, x.2 = InstTests.unitV) →
    List.Forall₂ (fun q x => NodeEnd hostI.length q.1 q.2 x) ps xs →
    ∃ M' inst es, Instantiates first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX r
        (importArgs hostI) M' inst es ∧
      M'.host = ((), logOfCalls (xs.map NodeRun.calls).flatten) ∧ NodesInv r xs M' inst es

/-- **Open goal, the export call from the invariant**: after an instantiation satisfying
`NodesInv` for the IR's node ends `xs`, the IR's first export `n` answering a call with no
arguments with `ws` is matched by a session call of the reference export `n` returning `ws`,
leaving the host state unchanged. -/
def Task.exportRefX : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (ps : List (Binary.CoreMod × List Impl)) (xs : List NodeRun) (n : String)
    (ws : List Silmaril.Wasm.Component.Val)
    (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)) (inst : InstId)
    (es : List (String × FuncId)),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    MultiImpFrag r → c.imports = hostI → c.nodes = coreNodes ps →
    (c.exports.map (·.name)).head? = some n →
    (∀ x ∈ (xs.map NodeRun.calls).flatten, x.2 = InstTests.unitV) →
    List.Forall₂ (fun q x => NodeEnd hostI.length q.1 q.2 x) ps xs →
    instPlay (F := sigU) (xs.map NodeRun.calls).flatten .ready ++
        [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    NodesInv r xs M inst es →
    ∃ f M', es.lookup n = some f ∧
      LinkedSession.SessRun first.prof (Host.ofEmbedder embL) M 0 [(f, [])]
        [some (ws.map toRefVal)] M' ∧ M'.host = M.host

/-! ## The export call, in pieces -/

/-- The IR function type `func() -> u32`. -/
abbrev getTy : FuncTy := ⟨[], [.u32]⟩

/-- **The IR's export phase at the node ends `xs`** (IR side): the reading's first export is the
option-less `canon lift` of type `func() -> u32` of export `e` of the environment, named `n`;
whenever `e` is export `i` (named `nm`) of the core instance `k` of the reading, that core instance
is the one of node `j` (after the inline instances of the definitions before the first core
instantiation), and the function exported as `nm` by the node's module instance, run in the store
its start function left without host calls, returns one `i32` value `v`, with `ws = [u32 v]`. -/
def ExportAt (r : RefComponent) (xs : List NodeRun) (n : String)
    (ws : List Silmaril.Wasm.Component.Val) : Prop :=
  ∃ (R : RSt) (e : Nat), refRead r = some R ∧
    R.exports.head? = some ⟨n, getTy, ⟨[.lift getTy], .call e⟩⟩ ∧
    ∀ (pre : RefComponent) (mi : Nat) (cargs : List (String × Nat)) (post : RefComponent)
      (k base i : Nat) (exps : CoreIface) (nm : String) (cft : CoreFuncTy),
      firstCore? r = some (pre, mi, cargs, post) → R.coreInsts[k]? = some (.node base exps) →
      exps[i]? = some (nm, cft) → e = base + i →
      ∃ (j : Nat) (x : NodeRun) (a : Nat) (c' : irEng.Config Nat) (v : BitVec 32),
        k = (preInsts pre).length + j ∧ xs[j]? = some x ∧
        (irEng.exports x.minst).lookup nm = some (.func a) ∧
        Silmaril.Wasm.Component.Engine.CoreEngine.Steps irEng (x.store, irEng.invoke a []) c' ∧
        irEng.status c'.1 c'.2 = .returned (.values [⟨.int .i32, v⟩]) ∧ ws = [.u32 v]

/-- **The IR's export phase** (IR only; proved: `MultiX.Thms.exportIR`): in the fragment, the IR's
instantiation play with the calls `t`, each answered `()`, followed by its first export `n`
answering a call with no arguments with `ws`, has node ends `xs` with the calls `t`
(`NodeEnd`, node by node) at which the export phase is `ExportAt r xs n ws`.

(The node ends are chosen by the play, not given: the instantiation and the export call are read
off one decomposition of the play, so the export's run starts from the store of the same start
run.) -/
def Task.exportIR : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (ps : List (Binary.CoreMod × List Impl)) (t : List (Σ _ : sigU.Op, Option Payload))
    (n : String) (ws : List Silmaril.Wasm.Component.Val),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    MultiImpFrag r → c.imports = hostI → c.nodes = coreNodes ps →
    (c.exports.map (·.name)).head? = some n →
    (∀ x ∈ t, x.2 = InstTests.unitV) →
    instPlay (F := sigU) t .ready ++
        [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    ∃ xs : List NodeRun, (xs.map NodeRun.calls).flatten = t ∧
      List.Forall₂ (fun q x => NodeEnd hostI.length q.1 q.2 x) ps xs ∧ ExportAt r xs n ws

/-- **The node's run in the shared core store** (proved: `MultiX.Thms.coreRunShared`): in the
fragment, a host-free run of an exported function of node `j` from the store its start function
left, returning the values `ys`, is a host-free run of the relocated function from the shared core
store (the node's store relocated along the gap `g`, followed by the objects `U` of later nodes,
typed), returning `ys`. (Without memories or tables only fresh structures and arrays, allocated
past `U`, are not at the relocated addresses. The reference engine's steps are its interpreter's,
complete for the relational semantics on typed stores: hence the typing of the shared store, which
`NodesInv` records.) -/
def Task.coreRunShared : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (ps : List (Binary.CoreMod × List Impl)) (xs : List NodeRun) (j : Nat)
    (p : Binary.CoreMod × List Impl) (x : NodeRun) (g : Gap (CanonHost (core3 neverFail)))
    (U : RStore) (nm : String) (a : Nat) (c' : irEng.Config Nat) (ys : List FlatValue),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → MultiImpFrag r →
    c.imports = hostI → c.nodes = coreNodes ps →
    List.Forall₂ (fun q x => NodeEnd hostI.length q.1 q.2 x) ps xs →
    ps[j]? = some p → xs[j]? = some x →
    g.PreOk (Silmaril.Proofs.Wasm.Component.Reference.Store.mapH gL x.store).funcs →
    Silmaril.Wasm.Execution.Core.StoreOk
      (Store.app (g.rel (Silmaril.Proofs.Wasm.Component.Reference.Store.mapH gL x.store)) U) →
    (irEng.exports x.minst).lookup nm = some (.func a) →
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps irEng (x.store, irEng.invoke a []) c' →
    irEng.status c'.1 c'.2 = .returned (.values ys) →
    ∃ y : (core3 neverFail).Config (CanonHost (core3 neverFail)),
      Silmaril.Wasm.Component.Engine.CoreEngine.Steps (core3 neverFail)
        (Store.app (g.rel (Silmaril.Proofs.Wasm.Component.Reference.Store.mapH gL x.store)) U,
          (core3 neverFail).invoke (g.fnMap a) []) y ∧
      (core3 neverFail).status y.1 y.2 = .returned (.values ys)

/-- **The session call through `canon lift`** (proved: `MultiX.Thms.callLift`): from a
configuration after an instantiation (host in control, no lockdown, nesting depth `0` (the
readiness condition of the host's `invoke`), one component instance, fresh or after one start
thread, no top-level calls, a typed core store whose host functions are the trampolines), a
session call of the option-less lift (instance `0`) at a type read
as `func() -> u32` of a core function whose host-free run from the core store returns one `i32`
`v` returns `u32 v`, leaving the host state unchanged. -/
def Task.callLift : Prop :=
  ∀ (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)) (f : FuncId) (a : Nat)
    (ty : Types.FuncType RtId) (y : (core3 neverFail).Config (CanonHost (core3 neverFail)))
    (v : BitVec 32),
    M.ctl = [] → M.store.lockdown = false → M.store.nestingDepth = 0 →
    (∃ ι, M.store.insts = [ι] ∧ InstOk ι) → M.pending = [] → M.results = [] →
    Silmaril.Wasm.Execution.Core.StoreOk M.store.core → HostTy M.store.core →
    ArenaField.funcs.get? M.store f = some (.lifted a ty {} ⟨0⟩) → TyRel ty getTy →
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps (core3 neverFail) (M.store.core, (core3 neverFail).invoke a []) y →
    (core3 neverFail).status y.1 y.2 = .returned (.values [⟨.int .i32, v⟩]) →
    ∃ M', LinkedSession.SessRun first.prof (Host.ofEmbedder embL) M 0 [(f, [])]
      [some [toRefVal (.u32 v)]] M' ∧ M'.host = M.host

end Silmaril.Wasm.Component.DecoderBridge
