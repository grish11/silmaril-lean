module

public import Silmaril.Wasm.Component.InstTests.Defs
public import Silmaril.Wasm.Component.InstRef.Defs
public import Silmaril.Wasm.Component.Conformance.ToRef.Defs

/-!
# Component test binaries on the reference machine

The reference machine (`Silmaril.Wasm.Component.Reference`) reads components in its own syntax,
`Core3Component`. The binaries are read into that syntax by `Conformance.decodeRef`: the verified
component grammar `Binary.parse`, then `Conformance.toRef`, which decodes the embedded core
modules with silmaril-lean's core decoder. `startsRef` and `trapRef` are the components it
returns on `startsBytes` and `trapBytes` (`InstTestsRef.Thms`: `decodeRef_starts`,
`decodeRef_trap`, by the kernel's definitional check); they are spelled out here so that they can
be read:

* `startsRef`: the type `func(x: u32)` and the import `f` of it; core modules `call1`, `call2`,
  `glob`; `canon lower` of `f` (core function `0`); the core instance exporting it as `"f"` (core
  instance `0`); the instances of `call1` and `call2` with it as `"env"` (core instances `1`,
  `2`) and of `glob` (core instance `3`); the type `func() -> u32`; `glob`'s `get`, aliased,
  `canon lift`ed and exported;
* `trapRef`: the same import; core modules `trap`, `call2`; `canon lower` of `f`; its core
  instance; the instances of `trap` (core instance `1`) and of `call2` with `"env"` (core
  instance `2`); `trap`'s `get`, aliased, lifted and exported.

The core modules are `Binary.coreModule call1CM`, …: the modules the core decoder reads from the
embedded bytes.

**The host.** The reference host is the logging host `InstRef.embL` (every import call answered
`()`, each call appended to a log). Its one host function has the type the binaries import,
`func(x: u32)` (`fWit`, `hostConfigX`). The reference machine compares parameter names when it
links an import, and the generic host configuration `LinkedSession.hostConfig hostI` names the
parameter `a`; the decoded components do not link against it.

`sessRunFrom` is `LinkedSession.sessRunBehaviours` from a given host configuration and root
arguments (`sessRunBehaviours … σ0 c ims` is `sessRunFrom … (hostConfig ims σ0) c (importArgs
ims)` by definition); `sessSummaryFrom` is its executable driver.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.InstTestsRef

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.InstLitmus Silmaril.Wasm.Component.InstTests

/-! ## The decoded components -/

/-- The type `func(x: u32)` (type `0`) and the import `f` of it (component function `0`). -/
def fImportDefs : List (Syntax.Definition Silmaril.Wasm.Module) :=
  [.type (.func { params := [("x", .prim .u32)], result := none }),
   .import_ { name := "f" } (.func 0)]

/-- The type `func() -> u32` (type `1`), core export `get` of core instance `inst` (core
function `1`), its `canon lift` (component function `1`) and the export `get` of it. -/
def getExportDefs (inst : Nat) : List (Syntax.Definition Silmaril.Wasm.Module) :=
  [.type (.func { params := [], result := some (.prim .u32) }),
   .alias (.coreExport inst "get" .func), .canon (.lift 1 [] 1),
   .export_ { name := "get" } ⟨.func, 1⟩ none]

/-- **`starts.wasm` in the reference machine's syntax** (`decodeRef startsBytes`). -/
def startsRef : Core3Component :=
  fImportDefs ++
  [.coreModule (Binary.coreModule call1CM), .coreModule (Binary.coreModule call2CM),
   .coreModule (Binary.coreModule globCM), .canon (.lower 0 []),
   .coreInstance (.exports [("f", ⟨.func, 0⟩)]), .coreInstance (.instantiate 0 [("env", 0)]),
   .coreInstance (.instantiate 1 [("env", 0)]), .coreInstance (.instantiate 2 [])] ++
  getExportDefs 3

/-- **`trap.wasm` in the reference machine's syntax** (`decodeRef trapBytes`). -/
def trapRef : Core3Component :=
  fImportDefs ++
  [.coreModule (Binary.coreModule trapCM), .coreModule (Binary.coreModule call2CM),
   .canon (.lower 0 []), .coreInstance (.exports [("f", ⟨.func, 0⟩)]),
   .coreInstance (.instantiate 0 []), .coreInstance (.instantiate 1 [("env", 0)])] ++
  getExportDefs 1

/-! ## The host -/

section Host

open Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine

/-- The type of the host function `f`: `func(x: u32)`, as the binaries import it. -/
def fWit : WIT.FuncType Empty RtId := ⟨[("x", .prim .u32)], none, false⟩

/-- **The host configuration of the binaries' import**: host function `0` of type `fWit`, the
logging host's initial state, the host in control. -/
def hostConfigX : Machine.Config LinkedSession.E0 (Unit × List HLinked2.HostEvent) :=
  Machine.Config.init (ArenaField.funcs.alloc CStore.empty (.host fWit ⟨0⟩)).1 ((), [])

variable {E : CoreEngine} [∀ a b, Decidable (E.ExternSub a b)] {σ : Type}

/-- **Session outcomes with the final host state, from configuration `m`**: instantiate `c` with
the root arguments `args`, then run the exports named in `calls` as a resumable session
(`LinkedSession.sessRunBehaviours` with the host configuration given). -/
def sessRunFrom (prof : ProfileKind) (h : Host E σ) (m : Machine.Config E σ)
    (c : CompAst E.Module) (args : Instantiate.Exports E) (calls : List (String × List Reference.Val)) :
    Set (List (Option (List Reference.Val)) × σ) :=
  {p | ∃ m₀ inst es fs m',
    InstResult.instance m₀ inst es ∈ instBehaviours prof h m c args ∧
    calls.mapM (fun q => es.lookup q.1) = some fs ∧
    LinkedSession.SessRun prof h m₀ 0 (fs.zip (calls.map Prod.snd)) p.1 m' ∧ p.2 = m'.host}

/-- `sessRunFrom`, executed (`LinkedSession.sessSummary` with the host configuration given). -/
def sessSummaryFrom (emb : Embedder E σ) (o : Oracle E) (fuel : Nat) (c : CompAst E.Module)
    (args : Instantiate.Exports E) (m : Machine.Config E σ) (calls : List (String × List Reference.Val)) :
    Option (List (Option (List Reference.Val)) × σ) :=
  (emb.instantiateRun o fuel c args m).bind fun (r, _, es) =>
    (calls.mapM fun q => es.lookup q.1).bind fun fs =>
      (LinkedSession.runSess emb o fuel r.config 0 (fs.zip (calls.map Prod.snd))).map
        fun p => (p.1, p.2.host)

end Host

end Silmaril.Wasm.Component.InstTestsRef
