module

public import Silmaril.Wasm.Component.Binary.Lower.Defs

/-!
# The named reading of a lowered component: function types with parameter names

`Binary.lower` produces IR function types (`FuncTy`) without parameter names: `func(x: u32)` and
`func(y: u32)` both lower to `⟨[u32], []⟩`. In the component model the names are part of the
type (component-model `a25fc0b`, `design/mvp/Explainer.md` line 639,
`functype ::= (func async? (param <labellit> <valtype>)* (result <valtype>)?)`, lines 877-879;
`Binary.md` lines 220-222, `paramlist ::= lt*:vec(<labelvaltype>)`), and type equality is
structural (`Explainer.md` lines 1046-1063, "type equality is defined to be AST equality"), so
the two are different types.

This module keeps them, without changing the IR (`Comp`, `FuncTy`, `Binary.lower`), which many
modules use:

* `NFuncTy`: a function type with named parameters; `NFuncTy.erase` forgets the names, giving
  the IR's `FuncTy`;
* `Lower.lowerSig a : NSig`: the **named imports and exports** of the AST `a`, in the order
  `Binary.lower` lists them (`Comp.imports`, `Comp.exports`): a pass over the sections that
  follows the lowering's type, function and instance index spaces (`Lower.section_`) and keeps
  each function type's parameter names (`namedFuncTy`: `Lower.funcTy`, the names zipped back
  in);
* `NComp`: an IR component together with its named signature; `lowerN`, `parseComponentN`:
  `Binary.lower`, `Binary.parseComponent` with the signature. `parseComponentN b` succeeds
  exactly when `parseComponent b` does (`DecoderBridge.Named.Thms`), with the same component.

`lowerSig` is total: an index out of range (where `Binary.lower` fails) reads as the empty
function type. That the names it reads are those of the reference reading of the same bytes,
and that erasing them gives the IR's types, is proved on the fragment `DecoderBridge.InFrag`
(`DecoderBridge.Named.Thms`); outside it nothing is proved.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Binary

open Silmaril.Wasm.Component

/-- **A component function type with parameter names**: the IR's `FuncTy` with each parameter
labelled. -/
structure NFuncTy where
  params : List (String × ValTy)
  results : List ValTy
  deriving Repr, DecidableEq, Inhabited

/-- Forget the parameter names. -/
def NFuncTy.erase (t : NFuncTy) : FuncTy := ⟨t.params.map (·.2), t.results⟩

/-- A named interface: function names with named function types. -/
abbrev NIface := List (String × NFuncTy)

/-- Forget the parameter names of every function of an interface. -/
def NIface.erase (I : NIface) : Iface := I.map fun p => (p.1, p.2.erase)

/-- **The named signature** of a lowered component: its imports and its exports, in order, with
named function types. -/
structure NSig where
  imports : NIface
  exports : NIface
  deriving Repr, DecidableEq, Inhabited

/-- **The named IR**: a lowered component and its named signature. -/
structure NComp where
  comp : Comp CoreMod
  sig : NSig

/-- The named imports. -/
def NComp.imports (n : NComp) : NIface := n.sig.imports

/-- The named exports. -/
def NComp.exports (n : NComp) : NIface := n.sig.exports

namespace Lower

/-- The empty function type, read where an index is out of range. -/
def nft0 : NFuncTy := ⟨[], []⟩

/-- **A function type with its parameter names**: the lowering's `funcTy`, with the names of the
parameters zipped back in (`none` where `funcTy` fails). -/
def namedFuncTy (types : Array TypeEntry) (f : FuncType) : Option NFuncTy :=
  match funcTy types f with
  | .ok ft => some ⟨(f.params.map (·.1)).zip ft.params, ft.results⟩
  | .error _ => none

/-- The named function type of a type definition, if it is a supported function type. -/
def namedDefType (types : Array TypeEntry) : DefType → Option NFuncTy
  | .func f => namedFuncTy types f
  | _ => none

/-- The function exports of an instance type with named types, as `instFuncs` reads them (the
local type space, outer aliases of count 1 reaching the enclosing types). -/
def instFuncsN (outer : List (TypeEntry × Option NFuncTy)) (decls : List InstanceDecl) :
    NIface :=
  (decls.foldl (fun (acc : List (TypeEntry × Option NFuncTy) × NIface) d =>
    let (loc, out) := acc
    match d with
    | .type t =>
      let tys := (loc.map (·.1)).toArray
      (loc ++ [(typeEntry tys t, namedDefType tys t)], out)
    | .alias ⟨.type, .outer 1 i⟩ =>
      (loc ++ [outer[i]?.getD (.other "outer type alias out of range", none)], out)
    | .alias ⟨.type, _⟩ => (loc ++ [(.other "aliased types", none)], out)
    | .export n (.func i) => (loc, out ++ [(n.name, ((loc[i]?).bind (·.2)).getD nft0)])
    | .export _ (.type _) => (loc ++ [(.other "exported (abstract) types", none)], out)
    | _ => (loc, out)) ([], [])).2

/-- **The state of the named pass**: the lowering's type space with the named function type of
each entry, the named type of each component function, the component instances (their function
exports, as function indices), and the imports and exports read so far. -/
structure SigSt where
  types : List (TypeEntry × Option NFuncTy) := []
  funcs : List NFuncTy := []
  insts : List (List (String × Nat)) := []
  imports : NIface := []
  exports : NIface := []

/-- The lowering's types. -/
def SigSt.tys (s : SigSt) : Array TypeEntry := (s.types.map (·.1)).toArray

/-- The named function type at type index `t`. -/
def SigSt.nty (s : SigSt) (t : Nat) : NFuncTy := ((s.types[t]?).bind (·.2)).getD nft0

/-- The named type of function `f`. -/
def SigSt.fn (s : SigSt) (f : Nat) : NFuncTy := s.funcs[f]?.getD nft0

/-- A type definition (`Lower.section_`, `.types`). -/
def sigType (s : SigSt) (t : DefType) : SigSt :=
  { s with types := s.types ++ [(typeEntry s.tys t, namedDefType s.tys t)] }

/-- An import (`Lower.import_`): a function import is the next import and function; an instance
import contributes its function exports, named `instance#function`, as imports and functions,
and a component instance. -/
def sigImport (s : SigSt) (i : Import) : SigSt :=
  match i.desc with
  | .func t =>
    { s with funcs := s.funcs ++ [s.nty t], imports := s.imports ++ [(i.name.name, s.nty t)] }
  | .instance t =>
    match s.types[t]? with
    | some (.inst ds, _) =>
      let fs := instFuncsN s.types ds
      { s with
        funcs := s.funcs ++ fs.map (·.2)
        imports := s.imports ++ fs.map fun (n, ft) => (s!"{i.name.name}#{n}", ft)
        insts := s.insts ++ [fs.zipIdx.map fun ((n, _), k) => (n, s.funcs.length + k)] }
    | _ => s
  | .type (.eq t) => { s with types := s.types ++ [s.types[t]?.getD (.other "bad type import", none)] }
  | .type .subResource => { s with types := s.types ++ [(.other "resources", none)] }
  | _ => s

/-- An alias (`Lower.alias_`): a function export of a component instance is a function; a type
alias is an unsupported type. -/
def sigAlias (s : SigSt) (a : Alias) : SigSt :=
  match a.sort, a.target with
  | .func, .export i n =>
    let f := ((s.insts[i]?.getD []).lookup n).getD s.funcs.length
    { s with funcs := s.funcs ++ [s.fn f] }
  | .type, _ => { s with types := s.types ++ [(.other "aliased instance types", none)] }
  | _, _ => s

/-- A canonical definition (`Lower.canon`): `canon lift` defines a function of its type. -/
def sigCanon (s : SigSt) : Canon → SigSt
  | .lift _ _ t => { s with funcs := s.funcs ++ [s.nty t] }
  | _ => s

/-- An export (`Lower.export_`): a function export is an export and a function; an exported
instance contributes its functions as exports named `instance#function`, and an instance; a type
export is a type. -/
def sigExport (s : SigSt) (e : Export) : SigSt :=
  match e.item.sort with
  | .func =>
    let ft := s.fn e.item.idx
    { s with exports := s.exports ++ [(e.name.name, ft)], funcs := s.funcs ++ [ft] }
  | .instance =>
    let inst := s.insts[e.item.idx]?.getD []
    { s with
      exports := s.exports ++ inst.map fun (n, f) => (s!"{e.name.name}#{n}", s.fn f)
      insts := s.insts ++ [inst] }
  | .type => { s with types := s.types ++ [s.types[e.item.idx]?.getD (.other "bad type export", none)] }
  | _ => s

/-- A component instance (`Lower.instance_`): its function exports. -/
def sigInstance (s : SigSt) : InstanceExpr → SigSt
  | .exports es =>
    { s with insts := s.insts ++ [es.filterMap fun (n, si) =>
        if si.sort = .func then some (n.name, si.idx) else none] }
  | .instantiate _ _ => s

/-- One section. -/
def sigSection (s : SigSt) : Section → SigSt
  | .types xs => xs.foldl sigType s
  | .imports xs => xs.foldl sigImport s
  | .aliases xs => xs.foldl sigAlias s
  | .canons xs => xs.foldl sigCanon s
  | .exports xs => xs.foldl sigExport s
  | .instances xs => xs.foldl sigInstance s
  | _ => s

/-- **The named signature of a component AST.** -/
def lowerSig (a : Ast) : NSig :=
  let s := a.sections.foldl sigSection {}
  ⟨s.imports, s.exports⟩

end Lower

/-- **Lowering with names**: `Binary.lower` and the named signature. -/
def lowerN (a : Ast) : Except String NComp := do
  let c ← lower a
  pure ⟨c, Lower.lowerSig a⟩

/-- **Driver entry point, with names**: `Binary.parseComponent` and the named signature. -/
def parseComponentN (bytes : ByteArray) : Except String NComp := do
  let ast ← match parse bytes with
    | .ok a => pure a
    | .error e => throw s!"component binary: {repr e.kind} at byte {e.pos}"
  lowerN ast

end Silmaril.Wasm.Component.Binary
