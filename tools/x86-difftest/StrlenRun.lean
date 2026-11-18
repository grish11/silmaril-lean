import Silmaril.X86.Str9G.Defs
/-! Whole-function check of the model on real glibc code (untrusted tooling): `__strlen_sse2`
of the pinned `libc.so.6` (Ubuntu 24.04 `libc6` 2.39-0ubuntu8.9 amd64, sha256
`3a15d66867d83762c7f2f1e37359cb8f6c5743edb369c65285cb0b1c4f7498bf`, read from
`$GLIBC_PINS/ubuntu_2_39_0ubuntu8_9/libc.so.6`, never copied; `run.sh` checks the hash), run by
`Str9G.step` from a System V call on random strings at random offsets and page positions
(including page-crossing first blocks), until it returns; the result must be the C `strlen`
of the string and the callee-saved registers must be unchanged.
Run from the package root: `tools/x86-difftest/run.sh strlen GLIBC_PINS_DIR`. -/
open Silmaril.X86

def fnOff : Nat := 0xc1a10      -- __strlen_sse2 (file offset = vaddr in this pin)
def fnLen : Nat := 412
def codeBase : Nat := 0x7f0000000000
def dataBase : Nat := 0x10000   -- three readable pages
def stackBase : Nat := 0x20000
def retAddr : Nat := 0xdead0000

/-- A tiny deterministic generator. -/
def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def runCase (code : List Byte) (seed : Nat) : Option String := Id.run do
  let mut r := lcg seed
  let pageOff := (r >>> 20) % 4096; r := lcg r
  let len := (r >>> 20) % (if r % 3 == 0 then 8 else 300); r := lcg r
  let s := dataBase + 4096 + pageOff - (if r % 2 == 0 then 0 else 0)
  -- data: random non-zero bytes, a NUL at s + len, random bytes after
  let data : List Byte := (List.range (3 * 4096)).map fun i =>
    let x := lcg (lcg (r + i))
    let a := dataBase + i
    let b : Nat := if a == s + len then 0 else if a ≥ s ∧ a < s + len then 1 + (x >>> 33) % 255 else (x >>> 33) % 256
    BitVec.ofNat 8 b
  if s + len ≥ dataBase + 3 * 4096 then return none
  let stack : List Byte := (List.range 8).map fun i => BitVec.ofNat 8 (retAddr >>> (8 * i))
  let mem : Silmaril.Process.Memory :=
    ⟨[⟨codeBase + fnOff, fnLen, ⟨true, false, true⟩⟩, ⟨dataBase, 3 * 4096, ⟨true, false, false⟩⟩,
      ⟨stackBase - 4096, 8192, ⟨true, true, false⟩⟩],
      Silmaril.Process.Memory.install (Silmaril.Process.Memory.install
        (Silmaril.Process.Memory.install ∅ (codeBase + fnOff) code) dataBase data) stackBase stack⟩
  let regs : Reg → Word := fun q => match q with
    | .rdi => BitVec.ofNat 64 s
    | .rsp => BitVec.ofNat 64 stackBase
    | q => BitVec.ofNat 64 (lcg (seed + q.toBitVec.toNat))
  let core : State := ⟨regs, BitVec.ofNat 64 (codeBase + fnOff), ⟨none, none, none, none, none, none⟩, 0⟩
  let mut g : Str9G.GState := ⟨⟨⟨core, mem⟩, fun _ => 0⟩, fun _ => 0, true⟩
  for _ in List.range 2000 do
    if g.x.m.core.rip.toNat == retAddr then break
    match Str9G.step g with
    | none => return some s!"seed {seed}: no step at +{g.x.m.core.rip.toNat - codeBase - fnOff}"
    | some g' => g := g'
  let c := g.x.m.core
  if c.rip.toNat != retAddr then return some s!"seed {seed}: did not return"
  if (c.read .rax).toNat != len then
    return some s!"seed {seed}: rax {(c.read .rax).toNat}, strlen {len} (s % 4096 = {s % 4096})"
  for q in [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] do
    if c.read q != core.read q then return some s!"seed {seed}: callee-saved {repr q}"
  if (c.read .rsp).toNat != stackBase + 8 then return some s!"seed {seed}: rsp"
  return none

def main : IO Unit := do
  let dir := (← IO.getEnv "GLIBC_PINS").getD "data/glibc"
  let f ← IO.FS.readBinFile s!"{dir}/ubuntu_2_39_0ubuntu8_9/libc.so.6"
  let code : List Byte := (List.range fnLen).map fun i => BitVec.ofNat 8 (f.get! (fnOff + i)).toNat
  let mut bad := 0
  let n := 300
  for k in List.range n do
    if let some e := runCase code (k * 7919 + 13) then
      bad := bad + 1
      if bad ≤ 20 then IO.println e
  IO.println s!"__strlen_sse2 on Str9G: {n} runs, {bad} failures"

#eval main
