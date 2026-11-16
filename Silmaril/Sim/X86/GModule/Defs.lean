module

public import Silmaril.Sim.X86.G.Thms

/-!
# The G simulator as an instantiated module (header)

For `Silmaril.Sim.X86.G.simModule`, instantiated by silmaril-lean's
`instantiateOnce?` in the empty store with no imports:

* `simInit`, `s₀`, `f₀`: the instantiation result, its store and frame;
* `exportExternAddr? mi n`, `exportGlobalVal s mi n`: what an embedder reads through the export
  named `n` (the module's "get" interface: one exported global per location);
* `locName i`: the export name of the global of ABI location `i` (`rax` … `of`);
* `loadStore σ`: the instantiated store with the location globals set to the encoding of the
  x86 state `σ` (what the host does with `global.set` on the exported mutable globals).

`Thms`: the instantiation succeeds and lays the 23 globals out at addresses `0..22`
(`f₀_globals`, by kernel evaluation); every location's export is its global
(`exportExternAddr_loc`); **the view `gval · f₀` is the exported-global read** (`gval_eq_export`);
and **loading**: `Enc (loadStore σ) f₀ σ` for every `σ`, with the code of `s₀` unchanged.
-/

@[expose] public section

namespace Silmaril.Sim.X86.GModule

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Sim.X86.G

/-- The address an export name resolves to in a module instance. -/
def exportExternAddr? (mi : ModuleInst) (n : String) : Option ExternAddr :=
  (mi.exports.find? (·.name == n)).map (·.addr)

/-- The value of the exported global `n` in the store `s` (an embedder's read). -/
def exportGlobalVal {H : Type} (s : Store H) (mi : ModuleInst) (n : String) : Option Val :=
  match exportExternAddr? mi n with
  | some (.global a) => (s.globals[a]?).map (·.value)
  | _ => none

/-- Export names of the ABI locations `0..22`. -/
def locNames : List String :=
  ["rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12",
    "r13", "r14", "r15", "rip", "cf", "pf", "af", "zf", "sf", "of"]

/-- The export name of ABI location `i`. -/
def locName (i : Nat) : String := locNames.getD i ""

/-- Instantiation of the G simulator in the empty store. -/
def simInit : Option (Store Nat × Frame × Option FuncIdx) :=
  instantiateOnce? ({} : Store Nat) simModule []

/-- The instantiated store. -/
def s₀ : Store Nat := (simInit.map (·.1)).getD {}

/-- The frame of the instantiated module. -/
def f₀ : Frame := (simInit.map (·.2.1)).getD {}

/-- The instantiated store loaded with the encoding of `σ` (code and everything else kept). -/
def loadStore (σ : Silmaril.X86.State) : Store Nat :=
  { s₀ with globals := (encStore (H := Nat) σ).globals }

end Silmaril.Sim.X86.GModule

/-! Old names (module `Silmaril.Sim.Wasm.X86G`). -/

namespace Silmaril.Sim.Wasm.X86G

@[deprecated Silmaril.Sim.X86.GModule.exportExternAddr? (since := "2026-11-10")]
alias exportAddr? := Silmaril.Sim.X86.GModule.exportExternAddr?
@[deprecated Silmaril.Sim.X86.GModule.exportGlobalVal (since := "2026-11-10")]
alias exportGlobalVal := Silmaril.Sim.X86.GModule.exportGlobalVal
@[deprecated Silmaril.Sim.X86.GModule.locNames (since := "2026-11-10")]
alias locNames := Silmaril.Sim.X86.GModule.locNames
@[deprecated Silmaril.Sim.X86.GModule.locName (since := "2026-11-10")]
alias locName := Silmaril.Sim.X86.GModule.locName
@[deprecated Silmaril.Sim.X86.GModule.simInit (since := "2026-11-10")]
alias simInit := Silmaril.Sim.X86.GModule.simInit
@[deprecated Silmaril.Sim.X86.GModule.s₀ (since := "2026-11-10")]
alias s₀ := Silmaril.Sim.X86.GModule.s₀
@[deprecated Silmaril.Sim.X86.GModule.f₀ (since := "2026-11-10")]
alias f₀ := Silmaril.Sim.X86.GModule.f₀
@[deprecated Silmaril.Sim.X86.GModule.loadStore (since := "2026-11-10")]
alias loadStore := Silmaril.Sim.X86.GModule.loadStore

end Silmaril.Sim.Wasm.X86G

end
