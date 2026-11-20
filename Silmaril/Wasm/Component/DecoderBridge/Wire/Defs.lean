module

public import Silmaril.Wasm.Component.DecoderBridge.Defs

/-!
# The two readings of a component binary: wiring, imports and exports (definitions)

`DecoderBridge.Rel` relates the IR reading `Binary.parseComponent` and the REF reading
`Conformance.decodeRef` of a binary on core instantiations only (which modules, in which order,
from which bytes). This module reads the **wiring** off the reference syntax, for a fragment of
the component model, so that it can be compared with the IR's.

## The wiring a reference component names

`refRead r : Option RSt` folds over the definitions of a reference component `r` and resolves,
in order, the index spaces the reference machine's instantiation (`Instantiate.instantiateDef`)
builds, **symbolically**: instead of store addresses, each entry is the IR wiring program
(`Impl`) it denotes over the IR's environment (the component's function imports, then the
function exports of the core instances, in order). The state `RSt`:

* `mods`: core modules (`coreModule m`);
* `types`: component function types (`type (func …)`), as IR function types (`refFuncTy`);
* `funcs`: component functions with their types: an import `k` is `call k`; `canon lift cf t`
  is `lift ft` before the wiring of core function `cf`; an export re-enters its function;
* `coreFuncs`: core functions: `canon lower g` is `lower ft` before the wiring of `g`; an alias
  of export `n` of core instance `i` is what `i` exports as `n` (`rciImpl`);
* `coreInsts`: core instances: the instance of a module (its base in the environment and its
  function exports), or an inline instance of core functions;
* `nodes`: for each core instantiation, the module and the wiring of each of its imports, which
  the instantiation's arguments resolve **by name**: import `(module, field)` is export `field`
  of the core instance the argument named `module` names (`List.lookup`, the first match, as
  in `Instantiate.coreImportFor?`);
* `imports`, `exports`: the component's function imports and exports, with their types.

`refRead` is `none` outside the fragment below. It mirrors the reference machine's name
resolution, but nothing here proves that the machine's run follows it: that is the semantic
correspondence, which is not proved.

## The fragment

`InFrag r` (decidable: `inFrag r = true`) says `refRead r` succeeds. The fragment is: top-level
definitions only, among

* core modules whose imports are all functions with numeric types (`coreIface`, the interface
  `Binary.Lower.coreMod` reads);
* function types whose parameters and result are primitive, not `string` or `error-context`,
  synchronous, with at most 16 flat parameters and 1 flat result;
* function imports;
* core instantiations whose imports all resolve, and inline core instances of core functions;
* aliases of core function exports of core instances;
* `canon lift` and `canon lower` with no options, `canon lower` only of a function that is not
  itself a lifted function (so not a lift-lower pair inside the component);
* exports of functions, without a type ascription.

So no instance imports or exports, nested components, component instances, values, start
definitions, resources or canon built-ins. Instance exports are excluded for a reason: the IR
reading flattens an exported instance `i` with a function `f` to an IR export named `i#f`,
while the reference machine reports the root instance's **function** exports only, so `i#f` is
not an export name there (`DecoderBridge.InstExport`).

## The relation

`RelW c r`: `refRead r` succeeds and the IR component `c` has its imports, its exports and, for
each node in order, the module and wiring that `refRead r` reads off `r`: node `k` of `c` is
`.core cm w` where `cm`'s bytes decode to the module of instantiation `k` of `r`, `cm`'s interface
is that module's (`coreIface`), and `w` is the wiring the instantiation's arguments name.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component

/-! ## Core module interfaces -/

/-- **The function interface of a decoded core module**, as `Binary.Lower.coreMod` reads it:
the module and field names of the imports, the imports with their types (all imports must be
functions with numeric types), and the function exports with their types. -/
def coreIface (m : Silmaril.Wasm.Module) :
    Except String (List (String × String) × CoreIface × CoreIface) := do
  let mut names := #[]
  let mut imps := #[]
  for i in m.imports do
    match i.type with
    | .func t =>
      names := names.push (i.moduleName, i.name)
      imps := imps.push (i.name, ← Binary.Lower.coreFuncTy m t)
    | _ => throw s!"core module imports a non-function ({i.moduleName} {i.name}); unsupported"
  let fts := m.functionTypes
  let mut exps := #[]
  for e in m.exports do
    match e.index with
    | .func f =>
      match fts[f.value.val]? with
      | some t => exps := exps.push (e.name, ← Binary.Lower.coreFuncTy m t)
      | none => throw s!"core export {e.name}: function {f.value.val} out of range"
    | _ => pure ()
  pure (names.toList, imps.toList, exps.toList)

/-! ## Function types -/

/-- A primitive value type of the fragment, as an IR value type (`string` and `error-context`
are not in the fragment). -/
def refPrim : Syntax.Prim → Option ValTy
  | .bool => some .bool | .s8 => some .s8 | .u8 => some .u8 | .s16 => some .s16
  | .u16 => some .u16 | .s32 => some .s32 | .u32 => some .u32 | .s64 => some .s64
  | .u64 => some .u64 | .f32 => some .f32 | .f64 => some .f64 | .char => some .char
  | .string => none | .errorContext => none

/-- A value type of the fragment: a primitive. -/
def refVT : Syntax.VT → Option ValTy
  | .prim p => refPrim p
  | .idx _ => none

/-- **A function type of the fragment**, as an IR function type: synchronous, primitive
parameters and result, at most 16 flat parameters and 1 flat result. -/
def refFuncTy (f : Syntax.FuncType) : Option FuncTy := do
  if f.async_ then none
  let ps ← f.params.mapM fun p => refVT p.2
  let rs ← match f.result with
    | none => some []
    | some t => (refVT t).map fun v => [v]
  let ft : FuncTy := ⟨ps, rs⟩
  if ft.flat.params.length > 16 then none
  if ft.flat.results.length > 1 then none
  some ft

/-! ## The symbolic reading -/

/-- A core instance, symbolically. -/
inductive RCI where
  /-- The instance of a module whose function exports `exps` start at `base` in the
  environment. -/
  | node (base : Nat) (exps : CoreIface)
  /-- An inline instance exporting core functions. -/
  | inline (es : List (String × Impl))

/-- The wiring of export `name` of a core instance: function `j` of a module instance is
environment function `base + j`; an inline instance exports the wiring it was given. -/
def rciImpl : RCI → String → Option Impl
  | .node base exps, name => (exps.findIdx? (·.1 == name)).map fun j => Impl.fwd (base + j)
  | .inline es, name => es.lookup name

/-- **The symbolic state of the reading**: the index spaces of the fragment, each entry the IR
wiring it denotes. -/
structure RSt where
  mods : List Silmaril.Wasm.Module := []
  types : List FuncTy := []
  funcs : List (Impl × FuncTy) := []
  coreFuncs : List Impl := []
  coreInsts : List RCI := []
  /-- The size of the environment: the function imports, then the core instances' exports. -/
  env : Nat
  nodes : List (Silmaril.Wasm.Module × List Impl) := []
  imports : Iface := []
  exports : List Export := []

/-- **One definition of the fragment**, read symbolically (`none` outside the fragment). -/
def refStep (R : RSt) : Syntax.Definition Silmaril.Wasm.Module → Option RSt
  | .coreModule m => some { R with mods := R.mods ++ [m] }
  | .type (.func f) => do
    let ft ← refFuncTy f
    some { R with types := R.types ++ [ft] }
  | .import_ n (.func t) => do
    let ft ← R.types[t]?
    some { R with funcs := R.funcs ++ [(⟨[], .call R.imports.length⟩, ft)],
                  imports := R.imports ++ [(n.name, ft)] }
  | .coreInstance (.instantiate mi args) => do
    let m ← R.mods[mi]?
    let (names, _, exps) ← (coreIface m).toOption
    let w ← names.mapM fun (mn, field) => do
      let j ← args.lookup mn
      let ci ← R.coreInsts[j]?
      rciImpl ci field
    some { R with nodes := R.nodes ++ [(m, w)], coreInsts := R.coreInsts ++ [.node R.env exps],
                  env := R.env + exps.length }
  | .coreInstance (.exports items) => do
    let es ← items.mapM fun (n, si) =>
      if si.sort = .func then (R.coreFuncs[si.idx]?).map ((n, ·)) else none
    some { R with coreInsts := R.coreInsts ++ [.inline es] }
  | .alias (.coreExport i n .func) => do
    let ci ← R.coreInsts[i]?
    let im ← rciImpl ci n
    some { R with coreFuncs := R.coreFuncs ++ [im] }
  | .canon (.lift f [] t) => do
    let im ← R.coreFuncs[f]?
    let ft ← R.types[t]?
    some { R with funcs := R.funcs ++ [(⟨.lift ft :: im.chain, im.target⟩, ft)] }
  | .canon (.lower g []) => do
    let (im, ft) ← R.funcs[g]?
    if im.chain ≠ [] then none
    some { R with coreFuncs := R.coreFuncs ++ [⟨.lower ft :: im.chain, im.target⟩] }
  | .export_ n ⟨.func, i⟩ none => do
    let (im, ft) ← R.funcs[i]?
    some { R with exports := R.exports ++ [⟨n.name, ft, im⟩], funcs := R.funcs ++ [(im, ft)] }
  | _ => none

/-- A function import definition. -/
def isFuncImport : Syntax.Definition Silmaril.Wasm.Module → Bool
  | .import_ _ (.func _) => true
  | _ => false

/-- **The symbolic reading of a reference component**: the environment starts after its
function imports. -/
def refRead (r : Conformance.RefComponent) : Option RSt :=
  r.foldlM refStep { env := (r.filter isFuncImport).length }

/-- The fragment, as a Boolean (kernel-checkable). -/
def inFrag (r : Conformance.RefComponent) : Bool := (refRead r).isSome

/-- **The fragment**: the symbolic reading succeeds. -/
def InFrag (r : Conformance.RefComponent) : Prop := inFrag r = true

instance (r : Conformance.RefComponent) : Decidable (InFrag r) :=
  inferInstanceAs (Decidable (inFrag r = true))

/-! ## The relation -/

/-- An IR node is the core instance of a module whose bytes decode to `m`, with the interface
`coreIface m`, and with the wiring `w`. -/
def NodeW (n : Node Binary.CoreMod) (p : Silmaril.Wasm.Module × List Impl) : Prop :=
  ∃ cm, n = .core cm p.2 ∧ Silmaril.Wasm.Binary.Core.decode? cm.bytes = some p.1 ∧
    coreIface p.1 = .ok (cm.importNames, CoreModule.imports cm, CoreModule.exports cm)

/-- **The wiring correspondence**: the imports, the exports and the nodes (module and wiring)
of the IR component are those the symbolic reading of the reference component names. -/
def RelW (c : Comp Binary.CoreMod) (r : Conformance.RefComponent) : Prop :=
  ∃ R, refRead r = some R ∧ c.imports = R.imports ∧ c.exports = R.exports ∧
    List.Forall₂ NodeW c.nodes R.nodes

end Silmaril.Wasm.Component.DecoderBridge
