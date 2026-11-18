module
public meta import Silmaril.Elf.Corpus.CjsonDetach.Equivalence.Thms
public meta section
open Silmaril.X86
open Silmaril.Elf.Corpus.CjsonDetach.Equivalence
private def sp : Nat := 33554440
private def exit : Nat := 40960
private def heap (base j : Nat) := base+128*j
private partial def execute (fuel : Nat) (s : Sse9.XState) : IO Sse9.XState := do
  if s.m.core.rip.toNat == exit then return s
  if fuel == 0 then throw <| IO.userError "fuel exhausted"
  match Sse9.step s with
  | some t => execute (fuel-1) t
  | none => throw <| IO.userError s!"SSE machine stuck at{s.m.core.rip.toNat}"
private def input (seed : Fin 8) : Input where
  address j := 1048576 + seed.val*1048584 + 128*j.val
  payload j k := BitVec.ofNat 8 (seed.val+j.val*31+k.val)
  aligned := by intro j; omega
  lower := by intro j; omega
  upper := by intro j; change 1048576 + seed.val*1048584 +128*j.val+64 < 140737488355328; omega
  disjoint := by intro j k neq; have h : j.val ≠ k.val := fun e => neq (Fin.ext e); omega
private def check (seed : Fin 8) : IO Unit := do
  let i := input seed
  let base := i.address 0
  let seed := seed.val
  let mut bytes : Silmaril.Process.ByteMemory := ∅
  for j in List.finRange 5 do
    bytes := Silmaril.Process.Memory.install bytes (i.address j)
      ((List.finRange 64).map fun k => initialByte i j k)
  bytes := Silmaril.Process.Memory.install bytes 23724 leftCode
  bytes := Silmaril.Process.Memory.install bytes 17248 rightCode
  bytes := Silmaril.Process.Memory.install bytes (sp-128) (List.replicate 256 0)
  let memory : Silmaril.Process.Memory := ⟨
    [⟨23724,leftCode.length,⟨true,false,true⟩⟩,⟨17248,rightCode.length,⟨true,false,true⟩⟩,⟨sp-128,256,⟨true,true,false⟩⟩] ++
    (List.range 5).map (fun j => ⟨heap base j,64,⟨true,j != 0 && j != 4,false⟩⟩),bytes⟩
  let some memory := Ext.storeN memory (BitVec.ofNat 64 sp) 8 (BitVec.ofNat 64 exit) | throw <| IO.userError "stack"
  let core := fun address => Silmaril.X86.State.mk (fun r => match r with
    | .rdi => BitVec.ofNat 64 (heap base 0)
    | .rsi => BitVec.ofNat 64 (heap base 2)
    | .rsp => BitVec.ofNat 64 sp
    | _ => BitVec.ofNat 64 (seed+r.toBitVec.toNat)) (BitVec.ofNat 64 address)
    ⟨some false,some false,some false,some false,some false,some false⟩ 0
  for j in List.finRange 5 do
    unless i.address j+65536 < sp do throw <| IO.userError "input stack separation rejected"
    for k in List.finRange 64 do
      unless memory.bytes.get? (i.address j+k.val) == some (initialByte i j k) do
        throw <| IO.userError "actual input payload rejected"
  let a : Sse9.XState := ⟨⟨core 23724,memory⟩,fun _ => BitVec.ofNat 128 (seed+111)⟩
  let b : Sse9.XState := ⟨⟨core 17248,memory⟩,a.xmm⟩
  unless initialBytesMatch i a.m do throw <| IO.userError "actual binary initial predicate rejected"
  for address in [i.address 0+16,i.address 2,i.address 4+32] do
    let wrong := (a.m.memory.bytes.get? address).getD 0 + 1
    let changed := {a.m with memory := {a.m.memory with bytes := a.m.memory.bytes.insert address wrong}}
    if initialBytesMatch i changed then throw <| IO.userError "altered child/next/unrelated payload accepted"
  let x ← execute 256 a
  let y ← execute 256 b
  unless x.m.core.read .rax == y.m.core.read .rax && x.m.core.read .rax == BitVec.ofNat 64 (heap base 2) do throw <| IO.userError "pointer mismatch"
  for (before,after,frame) in [(a,x,24),(b,y,0)] do
    unless after.m.core.read .rsp == BitVec.ofNat 64 (sp+8) do throw <| IO.userError "rsp"
    for r in [Reg.rbx,.rbp,.r12,.r13,.r14,.r15] do
      unless before.m.core.read r == after.m.core.read r do throw <| IO.userError "callee-saved"
    unless before.m.memory.regions == after.m.memory.regions && before.m.memory.bytes.size == after.m.memory.bytes.size do throw <| IO.userError "mappings/keys"
    for address in (List.range leftCode.length).map (23724+·) ++ (List.range rightCode.length).map (17248+·) ++ (List.range 256).map (sp-128+·) ++ (List.range 5).flatMap (fun j => (List.range 64).map (heap base j+·)) do
      let some value := before.m.memory.bytes.get? address | throw <| IO.userError "initial backing missing"
      let isUpdate := (heap base 1 ≤ address && address < heap base 1+8) ||
        (heap base 3+8 ≤ address && address < heap base 3+16) ||
        (heap base 2 ≤ address && address < heap base 2+16)
      unless isUpdate || (sp-frame ≤ address && address < sp) do
        unless after.m.memory.bytes.get? address == some value do throw <| IO.userError "unrelated byte changed"
  unless finalBytesMatch i x.m && finalBytesMatch i y.m do throw <| IO.userError "actual final predicate rejected"
  for address in [i.address 1,i.address 3+8,i.address 2,i.address 2+8,i.address 4+32] do
    let wrong := (x.m.memory.bytes.get? address).getD 0 + 1
    let changed := {x.m with memory := {x.m.memory with bytes := x.m.memory.bytes.insert address wrong}}
    if finalBytesMatch i changed then throw <| IO.userError "altered final pointer field/unrelated byte accepted"
  for j in List.finRange 5 do
    for k in List.finRange 64 do
      unless x.m.memory.bytes.get? (i.address j+k.val) == some (finalByte i j k) &&
          y.m.memory.bytes.get? (i.address j+k.val) == some (finalByte i j k) do
        throw <| IO.userError s!"exact mismatch seed{seed} object{j.val} byte{k.val} expected{(finalByte i j k).toNat} left{(x.m.memory.bytes.get? (i.address j+k.val)).map BitVec.toNat} right{(y.m.memory.bytes.get? (i.address j+k.val)).map BitVec.toNat}"
  for j in List.range 5 do
    for k in List.range 64 do
      unless x.m.memory.bytes.get? (heap base j+k) == y.m.memory.bytes.get? (heap base j+k) do throw <| IO.userError "caller heaps differ"
public def main : IO Unit := do
  for seed in List.finRange 8 do check seed
  IO.println "PASS8 local-only actual O0/O2 Sse9 detachment observations: shared memory, pointer return, exact allowed fields, unrelated bytes/mappings,24/0 frames; no registered equivalence or proof"
