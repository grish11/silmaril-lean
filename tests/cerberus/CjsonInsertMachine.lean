module
public meta import Silmaril.Elf.Corpus.CjsonInsert.Context.Defs
public meta section
open Silmaril.X86
open Silmaril.Elf.Corpus.CjsonInsert
private def sp : Nat := 8388616
private def exit : Nat := 40960
private partial def execute (fuel : Nat) (m : MState) : IO MState := do
 if m.core.rip.toNat == exit then return m
 if fuel == 0 then throw <| IO.userError "actual insertion fuel exhausted"
 match Open.step m with
 | some next => execute (fuel-1) next
 | none => throw <| IO.userError s!"actual insertion stuck at{m.core.rip.toNat}"
public def main : IO Unit := do
 for seed in List.range 4 do
  for index in ([1,3] : List Nat) do
   let base := 1048576+65536*seed
   let addr := fun j => base+64*j
   let mut bytes : Silmaril.Process.ByteMemory := ∅
   for (address,fragment) in excerpts do bytes := Silmaril.Process.Memory.install bytes address fragment
   bytes := Silmaril.Process.Memory.install bytes base ((List.range 384).map fun j => BitVec.ofNat 8 (j*31+seed*17))
   bytes := Silmaril.Process.Memory.install bytes (sp-256) ((List.range 264).map fun j => BitVec.ofNat 8 (j+seed))
   bytes := Silmaril.Process.Memory.install bytes sp (Ext.leBytes (BitVec.ofNat 64 exit) 8)
   for (j,off,k) in ([(0,16,1),(1,0,2),(1,8,3),(2,0,3),(2,8,1),(3,8,2)] : List (Nat × Nat × Nat)) do
    bytes := Silmaril.Process.Memory.install bytes (addr j+off) (Ext.leBytes (BitVec.ofNat 64 (addr k)) 8)
   for j in [3,4] do bytes := Silmaril.Process.Memory.install bytes (addr j) (Ext.leBytes 0 8)
   let regions := excerpts.map (fun (a,c) => (⟨a,c.length,⟨true,false,true⟩⟩ : Silmaril.Process.Region)) ++
     [⟨base,384,⟨true,true,false⟩⟩,⟨sp-256,264,⟨true,true,false⟩⟩]
   let memory : Silmaril.Process.Memory := ⟨regions,bytes⟩
   let before : MState := ⟨⟨(fun r => if r==.rsp then BitVec.ofNat 64 sp else
     if r==.rdi then BitVec.ofNat 64 base else if r==.rsi then BitVec.ofNat 64 (index+seed*2^32) else
     if r==.rdx then BitVec.ofNat 64 (addr 4) else BitVec.ofNat 64 (seed+r.toBitVec.toNat)),
     BitVec.ofNat 64 24266,⟨some false,some false,some false,some false,some false,some false⟩,0⟩,memory⟩
   let after ← execute 2000 before
   unless (after.core.read .rax).setWidth 32 == 1 && after.core.read .rsp == BitVec.ofNat 64 (sp+8) do
    throw <| IO.userError "actual insertion result/stack ABI mismatch"
   for r in [Reg.rbx,.rbp,.r12,.r13,.r14,.r15] do
    unless after.core.read r == before.core.read r do throw <| IO.userError "saved register changed"
   let updates := if index == 1 then [(4,0,2),(4,8,1),(2,8,4),(1,0,4)] else [(3,0,4),(4,8,3),(1,8,4)]
   let mut expected := before.memory.bytes
   for (j,off,k) in updates do expected := Silmaril.Process.Memory.install expected (addr j+off) (Ext.leBytes (BitVec.ofNat 64 (addr k)) 8)
   let mut restored := after.memory.bytes
   for j in List.range 128 do
    let address := sp-128+j
    let some value := before.memory.bytes.get? address | throw <| IO.userError "private frame backing missing"
    restored := restored.insert address value
   unless restored == expected && after.memory.regions == before.memory.regions do
    throw <| IO.userError "exact caller updates/unrelated bytes/mappings differ outside declared128-byte private frame"
   if seed == 0 && index == 1 then
    let readonly := {before with memory := {before.memory with regions := excerpts.map (fun (a,c) => ⟨a,c.length,⟨true,false,true⟩⟩) ++ [⟨base,384,⟨true,false,false⟩⟩,⟨sp-256,264,⟨true,true,false⟩⟩]}}
    match ← (try pure (some (← execute 2000 readonly)) catch e =>
      if (e.toString.splitOn "actual insertion stuck").length > 1 then pure none else throw e) with
    | some _ => throw <| IO.userError "readonly caller target accepted"
    | none => pure ()
 IO.println "PASS8 actual insertion/helper Open.step observations: four/interior or three/append exact pointer writes, full caller/unrelated byte and mapping preservation outside declared128-byte private frame, int32 ABI/high bits, saved registers and readonly target negative. Frame bound128 derived from actual top48/call8/add40/call8/suffix24 nesting and tested, not proved or registered; no semantic proof."
