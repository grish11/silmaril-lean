import Silmaril.X86.Str9G.Defs
/-! Differential check of `Str9G.step` against the native results in `out/cases.txt`
(`difftest.py`). Untrusted tooling. Run from the package root:
`lake env lean tools/x86-difftest/Check.lean`. -/
open Silmaril.X86

def hexNat (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10)) 0

def hexBytes (s : String) : List Byte :=
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i => BitVec.ofNat 8 (hexNat (String.ofList [cs[2*i]!, cs[2*i+1]!]))

def leNat (bs : List Byte) : Nat := bs.foldr (fun b n => b.toNat + 256 * n) 0

def flagsOf (f : Nat) : Flags :=
  ⟨some (f.testBit 0), some (f.testBit 2), some (f.testBit 4), some (f.testBit 6), some (f.testBit 7),
    some (f.testBit 11)⟩

def codeAddr : Nat := 0x70000000

def checkLine (l : String) : Option String := Id.run do
  let p := (l.splitOn " ").toArray
  let cls := p[0]!; let text := p[1]!
  let insn := hexBytes p[2]!
  let bufa := hexNat p[3]!; let fsb := hexNat p[4]!
  let rin := (List.range 16).map fun k => hexNat p[5 + k]!
  let fl := hexNat p[21]!
  let xin := hexBytes p[22]!; let min := hexBytes p[23]!
  let fault := p[24]! == "-"
  let rout := (List.range 16).map fun k => if fault then 0 else hexNat p[24 + k]!
  let regs : Reg → Word := fun r => BitVec.ofNat 64 (rin[r.toBitVec.toNat]!)
  let xs : Sse9.XFile := fun x =>
    BitVec.ofNat 128 (leNat ((xin.drop (16 * x.toBitVec.toNat)).take 16))
  let code := insn ++ List.replicate (64 - insn.length) (0x90 : Byte)
  let mem : Silmaril.Process.Memory :=
    ⟨[⟨codeAddr, 64, ⟨true, false, true⟩⟩, ⟨bufa, 512, ⟨true, true, false⟩⟩],
      Silmaril.Process.Memory.install (Silmaril.Process.Memory.install ∅ codeAddr code) bufa min⟩
  let core : State := ⟨regs, BitVec.ofNat 64 codeAddr, flagsOf fl, BitVec.ofNat 64 fsb⟩
  let t0 : Word := BitVec.ofNat 64 ((rout[2]! % 2^32) * 2^32 + rout[0]! % 2^32)
  let g0 : Str9G.GState := ⟨⟨⟨core, mem⟩, xs⟩, fun _ => t0, true⟩
  let mut g := g0
  let mut steps := 0
  let mut stuck := false
  while steps < 64 do
    match Str9G.step g with
    | none => stuck := true; break
    | some g' =>
      g := g'; steps := steps + 1
      if g.x.m.core.rip.toNat != codeAddr then break
  let tag := s!"{cls} {text} [{p[2]!}]"
  if fault then
    return if stuck && steps == 0 then none else some s!"{tag}: native faults, the model steps"
  if stuck then return some s!"{tag}: the model has no step after {steps}"
  let c := g.x.m.core
  if c.rip.toNat != codeAddr + insn.length then return some s!"{tag}: rip {c.rip.toNat - codeAddr}"
  let mut errs : List String := []
  for k in List.range 16 do
    if k != 4 then
      let r := Reg.ofBitVec (BitVec.ofNat 4 k)
      if (c.read r).toNat != rout[k]! then
        errs := errs ++ [s!"reg {k}: model {(c.read r).toNat} native {rout[k]!}"]
  let fo := hexNat p[40]!
  let chk (name : String) (m : Option Bool) (bit : Nat) : List String :=
    match m with
    | some b => if b != fo.testBit bit then [s!"flag {name}: model {b}"] else []
    | none => []
  errs := errs ++ chk "CF" c.flags.carry 0 ++ chk "PF" c.flags.parity 2 ++ chk "AF" c.flags.adjust 4 ++
    chk "ZF" c.flags.zero 6 ++ chk "SF" c.flags.sign 7 ++ chk "OF" c.flags.overflow 11
  let xo := hexBytes p[41]!
  for k in List.range 16 do
    let v := (g.x.xmm (Silmaril.X86.XReg.ofBitVec (BitVec.ofNat 4 k))).toNat
    if v != leNat ((xo.drop (16 * k)).take 16) then errs := errs ++ [s!"xmm{k}"]
  let mo := hexBytes p[42]!
  match g.x.m.memory.readBytes bufa 512 with
  | some bs => if bs != mo then errs := errs ++ ["memory"]
  | none => errs := errs ++ ["memory unreadable"]
  return if errs.isEmpty then none else some s!"{tag}: {errs}"

def main : IO Unit := do
  let ls ← IO.FS.lines "tools/x86-difftest/out/cases.txt"
  let mut bad := 0
  let mut byCls : Std.HashMap String (Nat × Nat) := {}
  for l in ls do
    if l.isEmpty then continue
    let cls := (l.splitOn " ")[0]!
    let r := checkLine l
    let (n, b) := byCls.getD cls (0, 0)
    byCls := byCls.insert cls (n + 1, b + (if r.isSome then 1 else 0))
    if let some e := r then
      bad := bad + 1
      if bad ≤ 60 then IO.println e
  for (c, (n, b)) in byCls.toList do IO.println s!"{c}: {n} cases, {b} mismatches"
  IO.println s!"total: {ls.size} cases, {bad} mismatches"

#eval main
