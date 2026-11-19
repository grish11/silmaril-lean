module
public meta import Silmaril.X86.Open.Thms
public meta section
open Silmaril.X86
private def functionCode : List (BitVec 8) := [0x48,0x8b,0x05,0xb1,0xb7,0x0f,0x00,0xc3]
private def address : Nat := 79888
private def got : Nat := 1109960
private def global : Nat := 972146
private def sp : Nat := 8388616
private def exit : Nat := 40960
private partial def execute (fuel : Nat) (s : MState) : IO MState := do
  if s.core.rip.toNat == exit then return s
  if fuel == 0 then throw <| IO.userError "fuel exhausted"
  match Open.step s with
  | some t => execute (fuel-1) t
  | none => throw <| IO.userError s!"stuck at{s.core.rip.toNat}"
public def main : IO Unit := do
  for seed in List.range 8 do
    let mut bytes : Silmaril.Process.ByteMemory := ∅
    bytes := Silmaril.Process.Memory.install bytes address functionCode
    bytes := Silmaril.Process.Memory.install bytes got (Ext.leBytes (BitVec.ofNat 64 global) 8)
    bytes := Silmaril.Process.Memory.install bytes global ("3.54.1".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat) ++ [0])
    bytes := Silmaril.Process.Memory.install bytes 2097152 ((List.range 64).map fun j => BitVec.ofNat 8 (seed+j))
    bytes := Silmaril.Process.Memory.install bytes sp (Ext.leBytes (BitVec.ofNat 64 exit) 8)
    let memory : Silmaril.Process.Memory := ⟨[⟨address,8,⟨true,false,true⟩⟩,⟨got,8,⟨true,false,false⟩⟩,
      ⟨global,7,⟨true,false,false⟩⟩,⟨2097152,64,⟨true,true,false⟩⟩,⟨sp,8,⟨true,false,false⟩⟩],bytes⟩
    let before : MState := ⟨⟨(fun r => if r==.rsp then BitVec.ofNat 64 sp else BitVec.ofNat 64 (seed+r.toBitVec.toNat)),BitVec.ofNat 64 address,
      ⟨some false,some false,some false,some false,some false,some false⟩,0⟩,memory⟩
    let after ← execute 8 before
    unless after.core.read .rax == BitVec.ofNat 64 global && after.core.read .rsp == BitVec.ofNat 64 (sp+8) do throw <| IO.userError "pointer/ABI mismatch"
    unless after.memory.bytes == before.memory.bytes && after.memory.regions == before.memory.regions do throw <| IO.userError "memory/mapping changed"
    for r in [Reg.rbx,.rbp,.r12,.r13,.r14,.r15] do
      unless after.core.read r == before.core.read r do throw <| IO.userError "saved register changed"
    let wrong := {before with memory := {before.memory with bytes := Silmaril.Process.Memory.install before.memory.bytes got (Ext.leBytes (BitVec.ofNat 64 (global+1)) 8)}}
    let changed ← execute 8 wrong
    if changed.core.read .rax == BitVec.ofNat 64 global then throw <| IO.userError "wrong GOT accepted as original pointer"
    let missing := {before with memory := {before.memory with bytes := before.memory.bytes.erase got}}
    if (Open.step missing).isSome then throw <| IO.userError "missing GOT backing accepted"
  IO.println "PASS8 local actual SQLite GOT-load machine observations: pointer RAX, saved registers/RSP, complete bytes/mappings preserved,0 private frame; wrong/missing GOT negatives; no registered context or semantic proof"
