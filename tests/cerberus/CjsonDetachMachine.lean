module

public meta import Silmaril.Elf.Corpus.CjsonDetach.Context.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Elf.Corpus.CjsonDetach
open Silmaril.X86
private def input : Context.Input where
  address j := 1048576 + 128*j.val
  payload j k := BitVec.ofNat 8 (j.val*31+k.val)
  aligned := by intro j; omega
  lower := by intro j; omega
  upper := by intro j; change 1048576+128*j.val+64 < 140737488355328; omega
  disjoint := by intro j k neq; have h : j.val ≠ k.val := fun e => neq (Fin.ext e); omega
private def sp : Nat := 8388616
private def exit : Nat := 40960
private partial def runMachine (n : Nat) (m : MState) : IO MState := do
  if m.core.rip.toNat == exit then return m
  if n == 0 then throw <| IO.userError "machine fuel exhausted"
  match Open.step m with
  | some next => runMachine (n-1) next
  | none => throw <| IO.userError s!"actual machine stuck at {m.core.rip.toNat}"
public def main : IO Unit := do
  let source ← match Context.prepare input with
    | .ok s => pure s
    | .error e => throw <| IO.userError e
  let expected ← match Context.expectedMemory input source.memory with
    | .ok s => pure s
    | .error e => throw <| IO.userError e
  let mut bytes : Silmaril.Process.ByteMemory := ∅
  for j in List.finRange 5 do
    for k in List.finRange 64 do
      let a := input.address j+k.val
      let some (some v) := source.memory.bytes.lookup (a : Int) | throw <| IO.userError "unspecified payload"
      bytes := bytes.insert a (BitVec.ofInt 8 v)
  bytes := Silmaril.Process.Memory.install bytes address code
  bytes := Silmaril.Process.Memory.install bytes (sp-128) (List.replicate 256 0)
  let memory : Silmaril.Process.Memory := ⟨
    [⟨address, code.length, ⟨true,false,true⟩⟩, ⟨sp-128,256,⟨true,true,false⟩⟩] ++
      (List.finRange 5).map (fun j => ⟨input.address j,64,⟨true, j.val != 0 && j.val != 4,false⟩⟩), bytes⟩
  let some memory := Ext.storeN memory (BitVec.ofNat 64 sp) 8 (BitVec.ofNat 64 exit)
    | throw <| IO.userError "return address initialization failed"
  let core : Silmaril.X86.State := ⟨(fun r => match r with
    | .rdi => BitVec.ofNat 64 (input.address 0)
    | .rsi => BitVec.ofNat 64 (input.address 2)
    | .rsp => BitVec.ofNat 64 sp
    | _ => BitVec.ofNat 64 (r.toBitVec.toNat+17)), BitVec.ofNat 64 address,
      ⟨some false,some false,some false,some false,some false,some false⟩, 0⟩
  let before : MState := ⟨core,memory⟩
  let after ← runMachine 256 before
  unless after.core.read .rsp == BitVec.ofNat 64 (sp+8) &&
      after.core.read .rax == BitVec.ofNat 64 (input.address 2) do
    throw <| IO.userError "wrong target pointer return/stack"
  for r in [Reg.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless after.core.read r == before.core.read r do throw <| IO.userError "callee-saved register changed"
  unless after.memory.regions == before.memory.regions do throw <| IO.userError "regions changed"
  for j in List.finRange 5 do
    for k in List.finRange 64 do
      let some (some value) := expected.bytes.lookup (input.address j+k.val : Int)
        | throw <| IO.userError "missing expected byte"
      unless after.memory.bytes.get? (input.address j+k.val) == some (BitVec.ofInt 8 value) do
        throw <| IO.userError s!"target heap differs at object{j.val}/byte{k.val}"
  for a in (List.range code.length).map (address+·) ++ (List.range 256).map (sp-128+·) do
    unless sp-24 ≤ a && a < sp do
      unless after.memory.bytes.get? a == before.memory.bytes.get? a do
        throw <| IO.userError "unrelated target memory changed"
  unless after.memory.bytes.size == before.memory.bytes.size do throw <| IO.userError "target byte key count changed"
  IO.println "PASS actual Open.step execution: returned item pointer, exact four heap writes, all320 caller bytes, callee-saved registers,24-byte private frame, unchanged other backing bytes and mappings; finite observation only"
