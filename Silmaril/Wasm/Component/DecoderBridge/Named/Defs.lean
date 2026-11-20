module

public import Silmaril.Wasm.Component.Binary.Lower.Named.Defs
public import Silmaril.Wasm.Component.DecoderBridge.Sem.Defs

/-!
# The two readings with parameter names (definitions)

The IR reading `Binary.parseComponent` drops parameter names (`Binary.Lower`), so the
hypothesis `c.imports = hostI` of `Task.startAdequacy` does not pin the specification type of
the import, and `paramname.wasm` (`f: func(y: u32)`) refutes it
(`DecoderBridge.ParamName.not_startAdequacy`). The named IR reading
`Binary.parseComponentN` (`Binary.Lower.Named`) keeps them. This module states what is compared:

* `refNFuncTy`, `RN`, `refNStep`, `refReadN`: the **named reading of a reference component**,
  the function types (with parameter names), functions, imports and exports that its
  definitions name, on the definition shapes of the fragment `InFrag` (`refStep`), `none`
  elsewhere;
* `hostFN`, `hostIN`: the host's import `f: func(x: u32)`, with its parameter name;
* `Task.startAdequacyNamed`: **the start goal on the named IR**: `Task.startAdequacy` with the
  import hypothesis `n.imports = hostIN` on the named IR reading. The root compatibility
  certificate `RootChecked` is not a hypothesis: on the fragment it follows from the named
  imports (`DecoderBridge.Named.Thms`, `rootChecked_of_named`).

## Exported instances: a restriction

The IR reading flattens an exported instance `i` with a function `f` into a function export
named `i#f`; the reference machine exports the instance `i` and reports only the root
instance's function exports (`DecoderBridge.InstExport`). This is **not** fixed here: the
comparison is restricted, by the decidable predicate `NoInstExport` (no definition exports an
instance), under which the export names of the named IR are the function export names of the
reference reading (`refFuncExportNames`), for every binary whose readings succeed
(`DecoderBridge.Named.Thms`, `exportNames_of_noInstExport`). `InFrag` implies it.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.Binary (NFuncTy NIface)
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTests Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)
open Silmaril.Games Silmaril.Games.Inst
open Silmaril.Wasm.SingleThreaded (profile neverFail)

/-! ## The named reading of a reference component -/

/-- **A function type of the fragment with its parameter names** (`refFuncTy`, the names
zipped back in). -/
def refNFuncTy (f : Syntax.FuncType) : Option NFuncTy :=
  (refFuncTy f).map fun ft => ⟨(f.params.map (·.1)).zip ft.params, ft.results⟩

/-- The state of the named reading: function types, functions, imports and exports. -/
structure RN where
  types : List NFuncTy := []
  funcs : List NFuncTy := []
  imports : NIface := []
  exports : NIface := []

/-- **One definition, named** (the shapes `refStep` reads; `none` on the others). -/
def refNStep (R : RN) : Syntax.Definition Silmaril.Wasm.Module → Option RN
  | .coreModule _ => some R
  | .type (.func f) => do
    let t ← refNFuncTy f
    some { R with types := R.types ++ [t] }
  | .import_ n (.func t) => do
    let ft ← R.types[t]?
    some { R with funcs := R.funcs ++ [ft], imports := R.imports ++ [(n.name, ft)] }
  | .coreInstance _ => some R
  | .alias (.coreExport _ _ .func) => some R
  | .canon (.lift _ [] t) => do
    let ft ← R.types[t]?
    some { R with funcs := R.funcs ++ [ft] }
  | .canon (.lower _ []) => some R
  | .export_ n ⟨.func, i⟩ none => do
    let ft ← R.funcs[i]?
    some { R with exports := R.exports ++ [(n.name, ft)], funcs := R.funcs ++ [ft] }
  | _ => none

/-- **The named reading of a reference component.** -/
def refReadN (r : RefComponent) : Option RN := r.foldlM refNStep {}

/-! ## The host's import, named -/

/-- The host function type `func(x: u32)`, with its parameter name. -/
def hostFN : NFuncTy := ⟨[("x", .u32)], []⟩

/-- **The host interface with parameter names**: `f: func(x: u32)` (`hostI` erases to it). -/
def hostIN : NIface := [("f", hostFN)]

/-! ## Exported instances -/

/-- No definition exports an instance (Boolean). -/
def noInstExport (r : RefComponent) : Bool :=
  r.all fun
    | .export_ _ ⟨.instance_, _⟩ _ => false
    | _ => true

/-- **The restriction on exports**: no definition exports an instance. -/
def NoInstExport (r : RefComponent) : Prop := noInstExport r = true

instance (r : RefComponent) : Decidable (NoInstExport r) :=
  inferInstanceAs (Decidable (noInstExport r = true))

/-- The names of the function export definitions of a reference component, in order. -/
def refFuncExportNames (r : RefComponent) : List String :=
  r.filterMap fun
    | .export_ n ⟨.func, _⟩ _ => some n.name
    | _ => none

/-! ## The start goal on the named IR -/

/-- **Open goal, the start goal on the named IR**: `Task.startAdequacy` with the import hypothesis
on the named IR reading (`n.imports = hostIN`, parameter name included). -/
def Task.startAdequacyNamed : Prop :=
  ∀ (b : ByteArray) (n : Binary.NComp) (r : RefComponent)
    (t : List (Σ _ : sigU.Op, Option Payload)) (nm : String) (ws : List Silmaril.Wasm.Component.Val),
    Binary.parseComponentN b = .ok n → decodeRef b = .ok r → (∃ ct, Valid Features.p2 r ct) →
    InFrag r → n.imports = hostIN → (n.comp.exports.map (·.name)).head? = some nm →
    (∀ x ∈ t, x.2 = InstTests.unitV) →
    instPlay (F := sigU) t .ready ++ [askEx (0, .vals []), ansEx (0, .vals []) (some (.vals ws))] ∈
      n.comp.denI (Binary.coreModSemI (profile neverFail)) →
    (([some (ws.map toRefVal)] : List (Option (List Value.Val))), ((), logOfCalls t)) ∈
      sessRunFrom first.prof (Host.ofEmbedder embL) hostConfigX r (importArgs hostI) [(nm, [])]

end Silmaril.Wasm.Component.DecoderBridge
