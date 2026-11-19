module

public import Silmaril.Wasm.Cfg.DanglingExn.Defs
public import Silmaril.Wasm.Cfg.DanglingTyped.Defs

@[expose] public section

/-!
# Threaded sessions with dangling host exceptions: definitions

A round of the instance session `InstSession.instSession I P s = threadS (instTripleS I P) s`
may answer an import call by an exception at a dangling address; Wasm code can then keep the
dangling reference and later allocate an exception naming itself, so the store after the round
need not be `StoreOk` (`ExampleAlias.alEnd_not_storeOk`) and the explicit domain `CfgInst.InstDom`
(which contains `ScalarInstance.WellFormed`, hence `StoreOk`) is not kept by the session
(`DanglingSession.not_instDom_alEnd`). The domain here is weaker than `StoreOk` and is kept.

* `FuncsWF I s`: the clauses of `ScalarInstance.WellFormed` that read only the store's functions
  (export addresses and types, host functions typed as imports), i.e. `WellFormed` without
  `StoreOk`;
* **`InstDomD I s`, the relaxed session domain**:
  - `funcs`: `FuncsWF I s`;
  - `chk`: the exception checker accepts the functions at the store's own tags
    (`StoreChkE (ehExt s.tags) s.funcs`);
  - `exns`: **the real store's exceptions are well formed at its real tags**
    (`Interp.ExnsOk s.tags s`): the tag of every exception instance of `s` is a tag of `s` and
    the instance has that tag's field count;
  - `okD`: the relaxed store invariant `DanglingTyped.StoreOkD s` (supported functions,
    `HeapBelow`, and a typing witness `gst s T X` that is `StoreOk`, whose exceptions at the real
    addresses carry the real tags and the real fields up to exception addresses).

  `DanglingSession.exn_typed` relates the last two: every real exception's tag is a real tag, and
  its fields are, up to exception addresses, values typed at that tag's parameter types (typed on
  the witness). No clause asserts `StoreOk s` or `acyclicExns`.
* `cfgInstSessionU I s`: the session of the CFG instance triple at the unrestricted universal
  host (`DanglingExn.cfgInstTripleU`), from the store `s`.

Theorems in `Silmaril.Wasm.Cfg.DanglingSession.Thms`.
-/

namespace Silmaril.Wasm.Cfg.DanglingSession

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp (StoreChkE ehExt)

variable (I : ScalarInstance)

/-- **The function clauses of `ScalarInstance.WellFormed`**: export addresses with their declared
types, host functions typed as imports. -/
structure FuncsWF (s : Store Nat) : Prop where
  addrs_length : I.addrs.length = I.exports.length
  export_type : ∀ j, ∃ fi : FuncInst Nat, s.funcs[I.addr j]? = some fi ∧
    Expand fi.type (I.exports.get j).toComp
  host_type : ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), s.funcs[a]? = some fi →
    fi.code = .host h → ∃ hlt : h < I.imports.length, Expand fi.type (I.imports.get ⟨h, hlt⟩).toComp

/-- **The relaxed session domain**: function clauses, checker acceptance at the store's tags,
the real exceptions well formed at the real tags, and the relaxed store invariant. -/
structure InstDomD (s : Store Nat) : Prop where
  funcs : FuncsWF I s
  chk : StoreChkE (ehExt s.tags) s.funcs
  exns : Interp.ExnsOk s.tags s
  okD : DanglingTyped.StoreOkD s

/-- **The CFG instance session at the unrestricted universal host.** -/
noncomputable def cfgInstSessionU (s : Store Nat) :
    DStrategy I.E (Abstract.InstSession.ssig I.exports) :=
  StratSession.threadS (DanglingExn.cfgInstTripleU I) s

end Silmaril.Wasm.Cfg.DanglingSession
