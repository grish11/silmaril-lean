module

public import Silmaril.Wasm.Component.DecoderBridge.FirstCore.Defs
public import Silmaril.Wasm.Component.InstWired.Defs

/-!
# The first core instantiation with lowered imports: the fragment

`FirstCore.Defs` names the binaries on which the case `k = 0` of `Task.failRefWired` is proved
when the first instantiated module has **no imports** (`FirstCoreFrag`). This module relaxes
that: the first instantiated module may import functions, provided they are exactly the
`canon lower` trampolines of the component's import `f: func(u32)` defined before it, in order.
The condition is decidable, on the REF reading:

* `preLowers pre`: the number of `canon lower` definitions before the first core
  instantiation (the core functions defined so far, `preOk` allowing no others);
* `preInsts pre`: the inline core instances defined before it, each as the names and core
  function indices of its items;
* `importIdx cargs insts mn nm`: the core function index the import `(mn, nm)` of the first
  instantiation resolves to: the argument named `mn` is a core instance, whose item `nm` is
  that core function (first matches, as `Instantiate.coreImportFor?` reads them);
* `importsLowered cargs insts m`: import `i` of `m` resolves to core function `i`;
* `irTypesOk m`: the interface the IR reads off `m` (`coreIface`) has only imports of the core
  type `fFlat = (func (param i32))`, the flattening of `func(x: u32)`;
* `refTypesOk m`: the validated import types of `m` (`Core3.importTypesE`) all accept a host
  function of that core type (`fExt`, the extern type of such a function);
* `FirstImpFrag r` (`firstImpFrag r = true`): `r` has a core instantiation; the definitions
  before it satisfy `preOk 0 0`; the module it instantiates has as many imports as there are
  `canon lower`s before it, and they satisfy the three conditions above. Unlike `FirstCoreFrag`,
  no split condition (`splitMod`) is needed: the module is instantiated against exactly the
  trampolines, so the two stores differ only in host code, and no relocation is involved.

`FirstCoreFrag' r := FirstCoreFrag r ∨ FirstImpFrag r` is the relaxed first-core fragment.
`starts.wasm` is in `FirstImpFrag` (`FirstImp.Thms.starts_firstImpFrag`); `trap.wasm` is in
`FirstCoreFrag` only (its first module has no imports, and a `canon lower` precedes it).

## Why the start function makes no host call in the failure goal

`Task.failRefWired` assumes the failing node is quiet (`NodeQuiet`): every import call of its
engine run is answered at once by its wiring, without a call of the component's imports. In the
fragment an import call of the start function is typed by `fFlat` (Core type soundness of the
IR's run), so its argument lifts to a `u32` and the `canon lower` wiring calls `f`: a quiet
failure has **no** import call at all. So the case covered here is: preparation of the module
against the trampolines fails, or its start function traps before its first import call.

## The remaining cases

`Task.failRefWiredRest'` is `Task.failRefWiredRest` restricted to the binaries outside the
relaxed fragment: a failing node `k ≥ 1`, or `¬ FirstCoreFrag' r`.
`FirstImp.Thms.failRefWiredRest_of_rest'` derives `Task.failRefWiredRest` from it.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance

variable {M : Type}

/-- The number of `canon lower` definitions in a list of definitions. -/
def preLowers : List (Syntax.Definition M) → Nat
  | [] => 0
  | .canon (.lower _ []) :: ds => preLowers ds + 1
  | _ :: ds => preLowers ds

/-- The inline core instances a list of definitions defines, in order: the names and core
function indices of their items. -/
def preInsts : List (Syntax.Definition M) → List (List (String × Nat))
  | [] => []
  | .coreInstance (.exports items) :: ds => items.map (fun p => (p.1, p.2.idx)) :: preInsts ds
  | _ :: ds => preInsts ds

/-- The core function index the import `(mn, nm)` resolves to, through the instantiation
arguments `cargs` and the inline core instances `insts`. -/
def importIdx (cargs : List (String × Nat)) (insts : List (List (String × Nat)))
    (mn nm : String) : Option Nat := do
  let j ← cargs.lookup mn
  let its ← insts[j]?
  its.lookup nm

/-- Import `i` of `m` resolves to core function `i`. -/
def importsLowered (cargs : List (String × Nat)) (insts : List (List (String × Nat)))
    (m : Silmaril.Wasm.Module) : Bool :=
  (List.range m.imports.length).all fun i =>
    match m.imports[i]? with
    | some imp => importIdx cargs insts imp.moduleName imp.name == some i
    | none => false

/-- The core type `(func (param i32))`, the flattening of `func(x: u32)`. -/
def fFlat : CoreFuncTy := ⟨[.int .i32], []⟩

/-- The interface the IR reads off `m` has only imports of core type `fFlat`. -/
def irTypesOk (m : Silmaril.Wasm.Module) : Bool :=
  match coreIface m with
  | .ok (_, imps, _) => imps.all (·.2 == fFlat)
  | .error _ => false

/-- A store with one host function of core type `fFlat`. -/
def fStore : Silmaril.Wasm.Execution.Core.Store Nat :=
  (Silmaril.Wasm.SingleThreaded.allocHost {} (Param.v1Type fFlat) 0).1

/-- The extern type of a host function of core type `fFlat`. -/
def fExt : Option Silmaril.Wasm.Component.Engine.Core3.ExtT :=
  Silmaril.Wasm.Component.Engine.Core3.externTypeE? fStore (.func 0)

/-- The validated import types of `m` all accept a host function of core type `fFlat`. -/
def refTypesOk (m : Silmaril.Wasm.Module) : Bool :=
  match fExt with
  | some τ => (Silmaril.Wasm.Component.Engine.Core3.importTypesE m).all fun p =>
      @decide (Silmaril.Wasm.Validation.ExternSub {} τ.1 p.2.2.1)
        (Silmaril.Wasm.Validation.ExternSub.decideEmpty τ.1 p.2.2.1 τ.2 p.2.2.2)
  | none => false

/-- The imports of the first instantiated module `m` are the `canon lower`s of `pre`, in
order, of the right types. -/
def impOk (pre : List (Syntax.Definition Silmaril.Wasm.Module)) (cargs : List (String × Nat))
    (m : Silmaril.Wasm.Module) : Bool :=
  decide (m.imports.length = preLowers pre) && importsLowered cargs (preInsts pre) m &&
    irTypesOk m && refTypesOk m

/-- The first-core fragment with lowered imports, as a Boolean (kernel-checkable). -/
def firstImpFrag (r : RefComponent) : Bool :=
  match firstCore? r with
  | none => false
  | some (pre, mi, cargs, _) =>
    preOk 0 0 pre &&
      match (coreMods pre)[mi]? with
      | some m => impOk pre cargs m
      | none => false

/-- **The first-core fragment with lowered imports**: the definitions before the first core
instantiation are of the forms `preOk` allows, and the module it instantiates imports exactly
the `canon lower`s defined before it, in order, at core type `fFlat`. -/
def FirstImpFrag (r : RefComponent) : Prop := firstImpFrag r = true

instance (r : RefComponent) : Decidable (FirstImpFrag r) :=
  inferInstanceAs (Decidable (firstImpFrag r = true))

/-- **The relaxed first-core fragment**: no imports (`FirstCoreFrag`), or lowered imports
(`FirstImpFrag`). -/
def FirstCoreFrag' (r : RefComponent) : Prop := FirstCoreFrag r ∨ FirstImpFrag r

instance (r : RefComponent) : Decidable (FirstCoreFrag' r) :=
  inferInstanceAs (Decidable (FirstCoreFrag r ∨ FirstImpFrag r))

open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-- **A node outcome with import calls**: the engine instance of the decoded module `cm`
answers `inst` with `a` (at `profile neverFail`) after the import calls `ys`, each answered by
its wiring `args` (over the `n` imports) with **one** call `x` of the component's imports,
whose answer is the call's: the calls `x` are `t`. (`NodeQuiet` is the case where every import
call is answered at once and `t = []`.) -/
def NodeCalls (n : Nat) (a : InstAns Unit) (cm : Binary.CoreMod) (args : List Impl)
    (t : List (Σ _ : sigU.Op, Option Payload)) : Prop :=
  ∃ ys : List (Σ _ : (sigN (CoreModule.imports cm).length).Op, Option Payload),
    EngineInst (core3P (profile neverFail))
      (Param.instOfI (core3P (profile neverFail)) (Binary.coreModule cm)
        (CoreModule.imports cm) (CoreModule.exports cm))
      (CoreModule.imports cm) ys a ∧
    List.Forall₂ (fun y x => ∃ k, implsN n args (CoreModule.imports cm).length y.1 = .call x.1 k ∧
      k x.2 = .pure y.2) ys t

/-- **Open goal, the cases of `Task.failRefWired` not covered by `FirstCore.Thms` and
`FirstImp.Thms`**: a failure of a node `k ≥ 1`, or a binary outside the relaxed first-core
fragment. -/
def Task.failRefWiredRest' : Prop :=
  ∀ (b : ByteArray) (c : Comp Binary.CoreMod) (r : RefComponent)
    (ps : List (Binary.CoreMod × List Impl)) (k : Nat) (hk : k < ps.length),
    (0 < k ∨ ¬ FirstCoreFrag' r) →
    Binary.parseComponent b = .ok c → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    HostWired r → c.imports = hostI → c.nodes = coreNodes ps →
    (∀ j (hj : j < k), NodeQuiet hostI.length .ready (ps[j]'(by omega)).1 (ps[j]'(by omega)).2) →
    NodeQuiet hostI.length (.fail ()) ps[k].1 ps[k].2 →
    InstResult.traps ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI)

end Silmaril.Wasm.Component.DecoderBridge
