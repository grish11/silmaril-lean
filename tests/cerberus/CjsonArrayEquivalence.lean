module
public meta import Silmaril.Elf.Corpus.CjsonArraySize.Equivalence.Thms
public meta section
open Silmaril.Elf.Corpus.CjsonArraySize.Equivalence
open Silmaril.X86
private def leftBytes : List (BitVec 8) := Silmaril.Elf.Corpus.CjsonArraySize.Equivalence.left.code
private def rightBytes : List (BitVec 8) := Silmaril.Elf.Corpus.CjsonArraySize.Equivalence.right.code
private def sp : Nat := 8388616
private def exit : Nat := 40960
private def heap (j : Nat) : Nat := 1048576+64*j
private partial def execute (fuel : Nat) (m : MState) : IO MState := do
  if m.core.rip.toNat == exit then return m
  if fuel == 0 then throw <| IO.userError "machine fuel exhausted"
  match Open.step m with
  | some next => execute (fuel-1) next
  | none => throw <| IO.userError s!"machine stuck at{m.core.rip.toNat}"
private def check (length : Nat) (null : Bool) (address frame : Nat) : IO (BitVec 32) := do
  let mut bytes : Silmaril.Process.ByteMemory := ∅
  bytes := Silmaril.Process.Memory.install bytes (heap 0) ((List.range ((length+1)*64)).map fun j => BitVec.ofNat 8 (j*31+length))
  bytes := Silmaril.Process.Memory.install bytes (heap 0+16) (Ext.leBytes (BitVec.ofNat 64 (if length==0 then 0 else heap 1)) 8)
  for j in List.range length do
    bytes := Silmaril.Process.Memory.install bytes (heap (j+1)) (Ext.leBytes (BitVec.ofNat 64 (if j+1<length then heap (j+2) else 0)) 8)
  bytes := Silmaril.Process.Memory.install bytes 21378 leftBytes
  bytes := Silmaril.Process.Memory.install bytes 16528 rightBytes
  bytes := Silmaril.Process.Memory.install bytes (sp-128) (List.replicate 256 0)
  let memory : Silmaril.Process.Memory := ⟨
    [⟨21378,leftBytes.length,⟨true,false,true⟩⟩,⟨16528,rightBytes.length,⟨true,false,true⟩⟩,⟨sp-128,256,⟨true,true,false⟩⟩,
     ⟨heap 0,(length+1)*64,⟨true,false,false⟩⟩],bytes⟩
  let some memory := Ext.storeN memory (BitVec.ofNat 64 sp) 8 (BitVec.ofNat 64 exit) | throw <| IO.userError "bad initial stack"
  let core : Silmaril.X86.State := ⟨(fun r => match r with
    | .rdi => BitVec.ofNat 64 (if null then 0 else heap 0)
    | .rsp => BitVec.ofNat 64 sp
    | _ => BitVec.ofNat 64 (r.toBitVec.toNat+17)), BitVec.ofNat 64 address,
      ⟨some false,some false,some false,some false,some false,some false⟩,0⟩
  let before : MState := ⟨core,memory⟩
  if h : length < 65 then
    let input : Input := ⟨null, ⟨length,h⟩, 1048576, (fun j => BitVec.ofNat 8 (j*31+length)), by decide, by decide, by decide⟩
    unless heapMatches input before do throw <| IO.userError "actual input bytes rejected"
    let location := heap 0+16
    let wrong := (before.memory.bytes.get? location).getD 0 + 1
    let altered := {before with memory := {before.memory with bytes := before.memory.bytes.insert location wrong}}
    if heapMatches input altered then throw <| IO.userError "changed child pointer accepted"
    let wrongPayload := {input with payload := fun j => if j==32 then input.payload j+1 else input.payload j}
    if heapMatches wrongPayload before then throw <| IO.userError "changed caller payload accepted"
  else throw <| IO.userError "out of declared finite domain"
  let after ← execute 2048 before
  unless after.core.read .rsp == BitVec.ofNat 64 (sp+8) do throw <| IO.userError "stack mismatch"
  for r in [Reg.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless after.core.read r == before.core.read r do throw <| IO.userError "callee-saved mutation"
  unless after.memory.regions == before.memory.regions && after.memory.bytes.size == before.memory.bytes.size do
    throw <| IO.userError "mapping/backing keys changed"
  for a in (List.range leftBytes.length).map (21378+·) ++ (List.range rightBytes.length).map (16528+·) ++ (List.range 256).map (sp-128+·) ++
      (List.range ((length+1)*64)).map (heap 0+·) do
    unless sp-frame ≤ a && a < sp do
      unless after.memory.bytes.get? a == before.memory.bytes.get? a do throw <| IO.userError s!"unrelated memory mutation at{a}"
  return (after.core.read .rax).setWidth 32
public def main : IO Unit := do
  for (n,null) in [(0,true)] ++ (List.range 65).map (·,false) do
    let a ← check n null 21378 32
    let b ← check n null 16528 0
    unless a == b do throw <| IO.userError s!"different actual loop returns at{n}"
  IO.println "PASS66 actual shared-initial-memory Open.step loop-pair observations: both genuine instruction streams, equal actual low32 returns, preserved caller memory/mappings/callee-saved state and exact32/0 private frames; registered obligation remains UNPROVED, no semantic proof; actual child/payload input negatives passed"
