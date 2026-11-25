module

public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Thms
public import Silmaril.Wasm.Institution.Operational.LegacyDivision.Core.Defs
public import Silmaril.Wasm.Lime1.ToCore.Instructions
public import Silmaril.Wasm.Institution.Operational.Thms
public import Silmaril.Wasm.Lime1.Execution.Step

/-! # The native Lime1 instantiation of the flat scalar rules -/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision.Lime1

open Silmaril.Logic.Operational
open Silmaril.Wasm.Lime1.Execution

def scalarSyntax : Syntax Silmaril.Wasm.Lime1.Instr :=
  ⟨value, fun t sign => .source (.intBinOp t (.div sign)), .source .nop⟩

def coreEncoding : CoreEncoding scalarSyntax where
  emit := Silmaril.Wasm.Lime1.Instr.toCore
  read := Silmaril.Wasm.Lime1.Instr.ofCore?
  read_emit := Silmaril.Wasm.Lime1.Instr.ofCore?_toCore
  value v := by rcases v with ⟨t, bits⟩; cases t <;> rfl
  divide _ _ := rfl
  nop := rfl

abbrev Supported := Admitted scalarSyntax
abbrev Derives := DerivesEdge scalarSyntax

/-- The same store, frame and ordered-code shape used by the Core institution. -/
def nativeShape (H : Type) : WasmShape := ⟨Store H, Silmaril.Wasm.Execution.Runtime.Frame, Admin, Unit⟩

def encode {H : Type} (c : Config H) : (WasmShape.signatures.obj (nativeShape H)).State :=
  ⟨(c.store, c.frame), c.code⟩

def decode {H : Type} (c : (WasmShape.signatures.obj (nativeShape H)).State) : Config H :=
  ⟨c.control.1, c.control.2, c.stack⟩

def nativeSystem {H : Type} (host : HostSemantics H) : WasmSystem :=
  ⟨nativeShape H, fun e => Supported (decode e.1).code ∧ Step host (decode e.1) (decode e.2.2)⟩

end Silmaril.Wasm.Institution.Operational.LegacyDivision.Lime1
