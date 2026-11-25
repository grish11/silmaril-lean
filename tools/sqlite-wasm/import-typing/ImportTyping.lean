module

public import SqliteWasm.ElementInit
public import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck

public section

namespace SqliteWasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

set_option maxRecDepth 65536
set_option maxHeartbeats 700000

private def fixtureTypes : List DefType :=
  ((sqlite.importedFunctions.mapM fun index => (allocTypes sqlite.types)[index.toNat]?).get rfl)

private theorem expectedImports :
    sqlite.imports.mapM (fun entry =>
      ({ types := allocTypes sqlite.types } : Context).closeExtern? entry.type) =
      some (fixtureTypes.map .func) := rfl

private theorem fixtureAddresses :
    externAddrsOk? reactorTypedImports reactorImportAddrs (fixtureTypes.map .func) = true := by
  decide +kernel

private theorem successfulLookup {A B : Type} (read : A → Option B)
    {xs : List A} {ys : List B}
    (each : List.Forall₂ (fun x y => read x = some y) xs ys) : xs.mapM read = some ys := by
  induction each with
  | nil => rfl
  | cons present tail replay =>
    simp [List.mapM_cons, present, replay]

/-- Ordinary validation's import type must be the one used by the canonical reactor fixture. -/
theorem reactorTypedAddressCompatibility {mt : CModuleType} (valid : ModuleOk sqlite mt) :
    List.Forall₂ (ExternAddrOk reactorTypedImports) reactorImportAddrs mt.imports := by
  cases valid with
  | mk typesOk importsOk =>
    rw [← allocTypes_eq typesOk] at importsOk
    have closures := successfulLookup
      (fun entry : Import => ({ types := allocTypes sqlite.types } : Context).closeExtern? entry.type)
      (importsOk.imp fun _ _ ok => ok.1)
    have declared := Option.some.inj (closures.symm.trans expectedImports)
    rw [declared]
    exact externAddrsOk?_sound fixtureAddresses


end SqliteWasm
