module

public import Silmaril.Wasm.Execution.Core.Store
public import Silmaril.Wasm.Lime1.Execution.Basic
public import Silmaril.Wasm.Lime1.ToCore
public import Silmaril.Wasm.V1.ToCore.DefTypes

/-! The Lime1-to-Core maps on numeric values, stores, frames and administrative
code. The runtime simulation and its side conditions are in
`Silmaril.Wasm.Versions.Thms`. -/

@[expose] public section

namespace Silmaril.Wasm.Lime1.Execution

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Validation (DefType Ty)

namespace ToCore

abbrev CVal := Silmaril.Wasm.Execution.Core.Val
abbrev CAdmin := Silmaril.Wasm.Execution.Core.Admin
abbrev CModuleInst := Silmaril.Wasm.Execution.Core.ModuleInst
abbrev CFrame := Silmaril.Wasm.Execution.Core.Frame
abbrev CStore (H : Type) := Silmaril.Wasm.Execution.Core.Store H
abbrev CConfig (H : Type) := Silmaril.Wasm.Execution.Core.Config H
abbrev CResult := Silmaril.Wasm.Execution.Core.Result
abbrev CHostOutcome (H : Type) := Silmaril.Wasm.Execution.Core.HostOutcome H
abbrev CHostSemantics (H : Type) := Silmaril.Wasm.Execution.Core.HostSemantics H

end ToCore

open ToCore

def _root_.Silmaril.Wasm.Execution.Runtime.Value.toCore (v : Value) : CVal := .num ⟨v.type, v.bits⟩

def _root_.Silmaril.Wasm.Execution.Runtime.ExternVal.toCore : ExternVal → Silmaril.Wasm.Execution.Core.ExternAddr
  | .func a => .func a.value
  | .table a => .table a.value
  | .memory a => .mem a.value
  | .global a => .global a.value

def _root_.Silmaril.Wasm.Execution.Runtime.ModuleInst.toCore (m : ModuleInst) : CModuleInst where
  types := m.types.map V1.FuncType.toDefType
  funcs := m.funcs.map Addr.value
  tables := m.tables.map Addr.value
  mems := m.memories.map Addr.value
  globals := m.globals.map Addr.value
  exports := m.exports.map fun e => ⟨e.name, e.value.toCore⟩

def _root_.Silmaril.Wasm.Execution.Runtime.Frame.toCore (f : Frame) : CFrame := ⟨f.locals.map (some ∘ Value.toCore), f.module.toCore⟩

variable {H : Type}

def _root_.Silmaril.Wasm.Execution.Runtime.FuncInst.toCore : FuncInst Func H → Silmaril.Wasm.Execution.Core.FuncInst H
  | .wasm t m c => ⟨t.toDefType, m.toCore, .wasm c.toCore⟩
  | .host t h => ⟨t.toDefType, {}, .host h⟩

def _root_.Silmaril.Wasm.Execution.Runtime.TableInst.toCore (t : TableInst) : Silmaril.Wasm.Execution.Core.TableInst :=
  ⟨⟨.i32, ⟨Fin.ofNat _ t.refs.length, t.max.map (Fin.ofNat _)⟩, Ty.funcref⟩,
    t.refs.map fun | none => .null | some a => .func a.value⟩

def _root_.Silmaril.Wasm.Execution.Runtime.MemInst.toCore (m : MemInst) : Silmaril.Wasm.Execution.Core.MemInst :=
  ⟨⟨.i32, ⟨Fin.ofNat _ (m.data.size / Silmaril.Wasm.Execution.Memory.pageSize), m.max.map (Fin.ofNat _)⟩⟩, m.data⟩

def _root_.Silmaril.Wasm.Execution.Runtime.GlobalInst.toCore (g : GlobalInst) : Silmaril.Wasm.Execution.Core.GlobalInst :=
  ⟨⟨g.mutability, .num g.value.type⟩, g.value.toCore⟩

def _root_.Silmaril.Wasm.Execution.Runtime.Store.toCore (s : Store H) : CStore H where
  funcs := s.funcs.map FuncInst.toCore
  tables := s.tables.map TableInst.toCore
  mems := s.memories.map MemInst.toCore
  globals := s.globals.map GlobalInst.toCore

/-- The defined type of the function at address `a` (default if absent). -/
def _root_.Silmaril.Wasm.Execution.Runtime.Store.funcDefType (s : Store H) (a : FuncAddr) : DefType :=
  ((s.funcs[a.value]?).map fun fi => fi.type.toDefType).getD default

mutual
def Admin.toCore (s : Store H) : Admin → List CAdmin
  | .source i => [.plain i.toCore]
  | .invoke a => [.ref (.func a.value), .callRefType (s.funcDefType a)]
  | .label n cont body => [.label n (cont.map Instr.toCore) (Admin.listToCore s body)]
  | .frame n f body => [.frame n f.toCore (Admin.listToCore s body)]
  | .trap => [.trap]

def Admin.listToCore (s : Store H) : List Admin → List CAdmin
  | [] => []
  | a :: as => Admin.toCore s a ++ Admin.listToCore s as
end

def _root_.Silmaril.Wasm.Execution.Runtime.Config.toCore (c : Config H) : CConfig H :=
  ⟨c.store.toCore, c.frame.toCore, Admin.listToCore c.store c.code⟩

def _root_.Silmaril.Wasm.Execution.Runtime.Result.toCore : Result → CResult
  | .values vs => .values (vs.map Value.toCore)
  | .trap => .trap

end Silmaril.Wasm.Lime1.Execution
