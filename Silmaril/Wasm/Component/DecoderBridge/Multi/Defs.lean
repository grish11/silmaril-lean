module

public import Silmaril.Wasm.Component.DecoderBridge.FirstImp.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Sem.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Sim.Defs

/-!
# Several core instantiations with lowered imports: the start goal, decomposed

`Task.startAdequacy` (`Sem.Defs`) is false outside the root checks (`DecoderBridge.ParamName`); its
corrected form `Task.startAdequacyChecked` is open. This module states it on a decidable fragment of
binaries with several core instantiations (`MultiImpFrag`, which `starts.wasm` is in), and splits
it into pieces, each a `Prop`; `Multi.Thms.startAdequacyFrag_of_nodes` derives the goal on the
fragment from them, so the decomposition is checked.

## The fragment

`MultiImpFrag r` (`multiImpFrag r = true`):

* `FirstImpFrag r` and `HostWired r`: the first core instantiation imports exactly the
  `canon lower` trampolines of `f: func(u32)` defined before it (`FirstImp.Defs`), and every core
  instance calls only the component's imports;
* `lowWired`: **every** node the REF reading names (`refRead`) instantiates a module whose
  imports have core type `fFlat = (func (param i32))` (`irTypesOk`), each wired to the lowering
  of the component's import `0` (`lowImpl`);
* `splitNodes`: every such node's module is in the split fragment (`splitMod`, below) and imports
  only functions (the first node included; there is no shared memory or table);
* `rootShape`: the definitions before the first core instantiation start with the type
  `func(x: u32)` and the import `f` of it, and import nothing else (the reference machine checks
  the root import against the host function `f: func(x: u32)` of `hostConfigX`, parameter names
  included: the IR reading drops them, so this is a condition on the REF reading alone);
* `postDefOk`: the definitions after it are core instantiations of modules in the split
  fragment (`splitMod`: no tags, memories, tables, data or element segments) whose imports
  resolve, through the inline core instances before the first instantiation, to trampolines, in
  order (import `i` to trampoline `i`, `importsLowered`), at types accepting the trampolines
  (`refTypesOk`), and which import only functions;
  primitive function types; aliases of core function exports (the core modules' export names
  distinct, so that an alias finds the export the IR wires); option-less `canon lift`s; and
  function exports;
* the component's first export has type `func() -> u32` (`isGetTy`), and the reading wires it as
  the option-less `canon lift` at that type of a function of the environment, with no other adapter
  (`liftsCall`: so not the lift of a `canon lower`ed import, nor an import re-exported).

## The reference machine at a definition

`RefAtDefs r post sc L M`: the reference machine, instantiating `r` from `hostConfigX` with the
root arguments `importArgs hostI` under the logging host `embL`, has run from the instantiation
host event, without host events or internal faults, to `M`, where the instantiation program runs
the remaining definitions `post` from the scope `sc` (followed by some continuation `K`), the
store is not locked down, and the host log is `L`.

## The pieces

* **(a)** `Task.nodeCallsIR` (IR only): in the fragment, a node-by-node instantiation of the IR's
  nodes with the calls `t` (each answered `()`) that is `ready` splits `t` into the calls `ts` of
  the nodes, each node instantiating with its calls as `NodeCalls` (each import call answered by
  its wiring with one call of `f`);
* **(b)** `Task.firstNodeRef`: if the IR's first node is ready after the calls `t₀`, the
  reference machine runs the definitions up to and including the first core instantiation
  (root checks, trampolines, the module's preparation, its start function with the host calls,
  and the **start function's epilogue**: the start task's return, back in the instantiation
  program), reaching `RefAtDefs r post sc (logOfCalls t₀) M` for the definitions `post` after it;
* **(b) and (c)**, `Task.nodesRef`: if the IR's nodes are ready after the calls `ts`, the machine
  runs the first core instantiation, the later core instantiations in the **shared core store**
  (where their imports resolve to the same trampolines, behind the objects of the earlier
  instances) and the other definitions, and finishes the instantiation (`Instantiates`) with the
  host log `logOfCalls ts.flatten`;
* **(d)** `Task.exportRef`: after a finished instantiation, the first export (a `canon lift` of
  type `func() -> u32`) answers a call with no arguments with the values the IR's first export
  answers, through a session call that leaves the host state unchanged.

The reference side of (b), (c) and (d) is stated at the first scheduling oracle (`first.prof`), as
in `Task.startAdequacy`. Every component of the fragment passes the root checks
(`Multi.Thms.rootChecked_of_multiImpFrag`), so `Task.startAdequacyFrag` is an instance of
`Task.startAdequacyChecked` (`Multi.Thms.startAdequacyFrag_of_checked`).

**Status** (`Multi.Thms`): (a), (b) and (b)+(c) are proved (`nodeCallsIR`, `firstNodeRef`,
`nodesRef`); (d) is open, and `startAdequacyFrag_of_d` derives `Task.startAdequacyFrag` from it.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Wasm.SingleThreaded (profile neverFail)

variable {M : Type}

/-! ## The fragment -/

/-- The wiring `lower(func(u32))` of the component's import `0`. -/
def lowImpl : Impl := ⟨[.lower ⟨[.u32], []⟩], .call 0⟩

/-- The wiring is `lowImpl`. -/
def isLowImpl : Impl → Bool
  | ⟨[.lower ⟨[.u32], []⟩], .call 0⟩ => true
  | _ => false

/-- Every node the REF reading names instantiates a module whose imports have core type
`fFlat`, each wired to `lowImpl`. -/
def lowWired (R : RSt) : Bool :=
  R.nodes.all fun p =>
    irTypesOk p.1 && decide (p.1.imports.length ≤ p.2.length) && p.2.all isLowImpl

/-- Every node the REF reading names instantiates a module in the split fragment (`splitMod`: no
tags, memories, tables, data or element segments) that imports only functions. (For the nodes
after the first, `postDefOk` checks this too; for the first node it is checked here.) -/
def splitNodes (R : RSt) : Bool :=
  R.nodes.all fun p =>
    splitMod p.1 && p.1.imports.all (fun i => match i.type with | .func _ => true | _ => false)

/-- The IR function type `func() -> u32`. -/
def isGetTy : FuncTy → Bool
  | ⟨[], [.u32]⟩ => true
  | _ => false

/-- The wiring is `lift(func() -> u32)` of a call of an environment function, with no other
adapter. -/
def liftsCall : Impl → Bool
  | ⟨[.lift ft], .call _⟩ => isGetTy ft
  | _ => false

/-- The component function type `func(x: u32)`. -/
def fFuncType : Syntax.FuncType := { params := [("x", .prim .u32)], result := none }

/-- No definition is an import. -/
def noImport (ds : List (Syntax.Definition M)) : Bool :=
  ds.all fun d => match d with
    | .import_ _ _ => false
    | _ => true

/-- The definitions start with the type `func(x: u32)` and the import `f` of it, and import
nothing else. -/
def rootShape : List (Syntax.Definition M) → Bool
  | .type (.func ft) :: .import_ n (.func 0) :: ds =>
    decide (ft = fFuncType) && decide (n = { name := "f" }) && noImport ds
  | _ => false

/-- The imports of `m` resolve, through the instantiation arguments `cargs` and the inline core
instances `insts`, to core functions below `n`. -/
def importsBelow (cargs : List (String × Nat)) (insts : List (List (String × Nat)))
    (n : Nat) (m : Silmaril.Wasm.Module) : Bool :=
  m.imports.all fun imp =>
    match importIdx cargs insts imp.moduleName imp.name with
    | some i => decide (i < n)
    | none => false

/-- A definition after the first core instantiation, with `n` trampolines, the inline core
instances `insts` and the core modules `mods` defined before it. -/
def postDefOk (n : Nat) (insts : List (List (String × Nat))) (mods : List Silmaril.Wasm.Module) :
    Syntax.Definition Silmaril.Wasm.Module → Bool
  | .coreInstance (.instantiate mi cargs) =>
    match mods[mi]? with
    | some m => splitMod m && irTypesOk m && importsBelow cargs insts n m &&
        importsLowered cargs insts m && refTypesOk m &&
        m.imports.all (fun i => match i.type with | .func _ => true | _ => false)
    | none => false
  | .type (.func ft) => funcTypePrim ft
  | .alias (.coreExport _ _ .func) => mods.all fun m => (m.exports.map (·.name)).Nodup
  | .canon (.lift _ [] _) => true
  | .export_ _ ⟨.func, _⟩ none => true
  | _ => false

/-- The fragment of several core instantiations with lowered imports, as a Boolean
(kernel-checkable). -/
def multiImpFrag (r : RefComponent) : Bool :=
  firstImpFrag r && hostWired r &&
    (match refRead r with
      | some R => lowWired R && (R.exports.head?.map fun e => isGetTy e.ty).getD false &&
          splitNodes R && (R.exports.head?.map fun e => liftsCall e.impl).getD false
      | none => false) &&
    (match firstCore? r with
      | some (pre, _, _, post) =>
        rootShape pre && post.all (postDefOk (preLowers pre) (preInsts pre) (coreMods pre))
      | none => false)

/-- **The fragment of several core instantiations with lowered imports.** -/
def MultiImpFrag (r : RefComponent) : Prop := multiImpFrag r = true

instance (r : RefComponent) : Decidable (MultiImpFrag r) :=
  inferInstanceAs (Decidable (multiImpFrag r = true))

/-! ## The reference machine at a definition -/

/-- **The reference machine at the definitions `post`**: instantiating `r` from `hostConfigX`
under the logging host, it has run from the instantiation host event, without host events or
internal faults, to `M`, where the instantiation program runs the definitions `post` from the
scope `sc`; the store is not locked down and the host log is `L`. -/
def RefAtDefs (r post : RefComponent) (sc : Instantiate.Scope (core3 neverFail))
    (L : List HLinked2.HostEvent)
    (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)) : Prop :=
  (∃ tr, Steps first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX
      (.host (instantiateTop r (importArgs hostI)) :: tr) M ∧
    (∀ ev, Label.host ev ∉ tr) ∧ (∀ msg, Label.trap (.internal msg) ∉ tr)) ∧
  (∃ K : Instantiate.Scope (core3 neverFail) →
      Canon.P (core3 neverFail) (Unit × List HLinked2.HostEvent) (Ret (core3 neverFail)),
    M.ctl = [.ofProg none (post.foldlM (Instantiate.instantiateDef Instantiate.callRecurse ⟨0⟩ []
      (importArgs hostI)) sc >>= K)]) ∧
  M.store.lockdown = false ∧ M.host = ((), L)

/-! ## The pieces -/

/-- **Piece (a), the IR's node calls** (proved: `Multi.Thms.nodeCallsIR`): in the fragment, a ready
node-by-node instantiation with the calls `t`, each answered `()`, is the nodes' instantiations with
the calls `ts`, in order, each as `NodeCalls`. -/
def Task.nodeCallsIR : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (ps : List (Binary.CoreMod × List Impl)) (t : List (Σ _ : sigU.Op, Option Payload)),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → MultiImpFrag r →
    c.imports = hostI → c.nodes = coreNodes ps → (∀ x ∈ t, x.2 = InstTests.unitV) →
    NodesInst (Binary.coreModSemI (profile neverFail)) hostI.length ps t .ready →
    ∃ ts : List (List (Σ _ : sigU.Op, Option Payload)), t = ts.flatten ∧
      List.Forall₂ (fun p tj => NodeCalls hostI.length .ready p.1 p.2 tj) ps ts

/-- **Piece (b), the first node with its start epilogue** (proved: `Multi.Thms.firstNodeRef`): if
the IR's first node is ready after the calls `t₀`, the reference machine runs the definitions up to
and including the first core instantiation, with the host log `logOfCalls t₀`. -/
def Task.firstNodeRef : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (p : Binary.CoreMod × List Impl) (ps : List (Binary.CoreMod × List Impl))
    (t₀ : List (Σ _ : sigU.Op, Option Payload)) (pre : RefComponent) (mi : Nat)
    (cargs : List (String × Nat)) (post : RefComponent),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → MultiImpFrag r →
    c.imports = hostI → c.nodes = coreNodes (p :: ps) → (∀ x ∈ t₀, x.2 = InstTests.unitV) →
    NodeCalls hostI.length .ready p.1 p.2 t₀ →
    firstCore? r = some (pre, mi, cargs, post) →
    ∃ sc M, RefAtDefs r post sc (logOfCalls t₀) M

/-- **Open goal, piece (d), the export phase**: after a finished instantiation, the IR's first
export `n` answering a call with no arguments with `ws` is matched by a session call of the
reference export `n` returning `ws`, leaving the host state unchanged. -/
def Task.exportRef : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (t : List (Σ _ : sigU.Op, Option Payload)) (n : String) (ws : List Silmaril.Wasm.Component.Val)
    (M : Machine.Config (core3 neverFail) (Unit × List HLinked2.HostEvent)) (inst : InstId)
    (es : List (String × FuncId)),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    MultiImpFrag r → c.imports = hostI → (c.exports.map (·.name)).head? = some n →
    (∀ x ∈ t, x.2 = InstTests.unitV) →
    instPlay (F := sigU) t .ready ++ [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    Instantiates first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX r
      (importArgs hostI) M inst es →
    ∃ f M', es.lookup n = some f ∧
      LinkedSession.SessRun first.prof (Host.ofEmbedder embL) M 0 [(f, [])]
        [some (ws.map toRefVal)] M' ∧ M'.host = M.host


/-- **Pieces (b) and (c) together, the instantiation**: in the fragment, if the IR's nodes are
ready after the calls `ts`, each answered `()`, the reference machine finishes the instantiation
with the host log `logOfCalls ts.flatten`.

(It asks for the instantiation from the start rather than from `RefAtDefs`, whose continuation `K`
of the definitions is only an existential: nothing in it says that `K` finishes the
instantiation. The proof, `Multi.Thms.nodesRef`, tracks the continuation.) -/
def Task.nodesRef : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (ps : List (Binary.CoreMod × List Impl)) (ts : List (List (Σ _ : sigU.Op, Option Payload))),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → MultiImpFrag r →
    c.imports = hostI → c.nodes = coreNodes ps →
    (∀ x ∈ ts.flatten, x.2 = InstTests.unitV) →
    List.Forall₂ (fun q tj => NodeCalls hostI.length .ready q.1 q.2 tj) ps ts →
    ∃ M' inst es, Instantiates first.prof embL.hr (Host.ofEmbedder embL).dispatch hostConfigX r
        (importArgs hostI) M' inst es ∧
      M'.host = ((), logOfCalls ts.flatten)

/-- **`Task.startAdequacy` on the fragment `MultiImpFrag`** (where it is `Task.startAdequacyChecked`). -/
def Task.startAdequacyFrag : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (t : List (Σ _ : sigU.Op, Option Payload)) (n : String) (ws : List Silmaril.Wasm.Component.Val),
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    MultiImpFrag r → c.imports = hostI → (c.exports.map (·.name)).head? = some n →
    (∀ x ∈ t, x.2 = InstTests.unitV) →
    instPlay (F := sigU) t .ready ++ [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
      c.denI (Binary.coreModSemI (profile neverFail)) →
    (([some (ws.map toRefVal)] : List (Option (List Value.Val))), ((), logOfCalls t)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) [(n, [])]

end Silmaril.Wasm.Component.DecoderBridge
