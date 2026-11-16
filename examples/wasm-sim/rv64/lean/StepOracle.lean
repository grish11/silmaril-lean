/-
Executable oracle: runs `Silmaril.RiscV.Ext.MState.step` (the Lean RV64 model,
Silmaril/Raw/Machine/RiscV/Ext/Machine.lean) on test cases read from stdin, for
differential testing of the Wasm simulators (`wasm-sim-rv lean-oracle`).

Memory: two backed regions, code [0x10000, 0x11000) r-x and data
[0x20000, 0x21000) rw-, all zero except the instruction word.
Input lines:  `<word> <pc> <x0> ... <x31>` (decimal).
Output lines: `R <pc> <x1> ... <x31> <dw>` (retired; dw = the doubleword at the
store address rounded down to 8, or `-`), or `S` (stopped), `F` (fetch fault),
`U` (undecodable), `TM` / `DM` / `DF` (target misaligned, data misaligned,
data fault).
Run: `lake env lean --run StepOracle.lean < cases.txt` in a Silmaril checkout
with `Silmaril.Machine.RiscV.Ext.Machine.Defs` built.
-/
import Silmaril.Machine.RiscV.Ext.Machine.Defs

open Silmaril Silmaril.RiscV Silmaril.RiscV.Ext Silmaril.Process

def codeRegion : Region := ⟨0x10000, 0x1000, ⟨true, false, true⟩⟩
def dataRegion : Region := ⟨0x20000, 0x1000, ⟨true, true, false⟩⟩

def baseMemory : Memory :=
  { regions := [codeRegion, dataRegion],
    bytes := Memory.install (Memory.install ∅ 0x10000 (List.replicate 0x1000 0))
      0x20000 (List.replicate 0x1000 0) }

def mkState (pc : Nat) (xs : Array Nat) : State :=
  { regs := fun r => BitVec.ofNat 64 (xs.getD r.toNat 0), pc := BitVec.ofNat 64 pc }

def leNat (bytes : List Process.Byte) : Nat :=
  bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

def storeAddress (word : BitVec 32) (s : State) : Option Nat :=
  match Ext.decode word with
  | some (.store _ rs1 _ offset) => some ((effectiveAddress s rs1 offset).toNat / 8 * 8)
  | _ => none

def runCase (line : String) : String :=
  let nums := (line.splitOn " ").filter (· ≠ "") |>.map String.toNat!
  match nums with
  | word :: pc :: xs =>
    let w : BitVec 32 := BitVec.ofNat 32 word
    let s := mkState pc xs.toArray
    let mem := { baseMemory with bytes := Memory.install baseMemory.bytes pc (wordBytes w) }
    match (MState.step ⟨s, mem⟩) with
    | .retired next =>
      let regs := (List.range 31).map fun i => toString (next.core.read (BitVec.ofNat 5 (i + 1))).toNat
      let dw := match storeAddress w s with
        | some a => match next.memory.readBytes a 8 with
          | some bytes => toString (leNat bytes)
          | none => "-"
        | none => "-"
      "R " ++ toString next.core.pc.toNat ++ " " ++ " ".intercalate regs ++ " " ++ dw
    | .stopped => "S"
    | .fetchFault => "F"
    | .undecodable _ => "U"
    | .targetMisaligned _ _ => "TM"
    | .dataMisaligned _ _ => "DM"
    | .dataFault _ _ => "DF"
  | _ => "?"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let l := line.trimAsciiEnd.toString
  if !l.isEmpty then stdout.putStrLn (runCase l)
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
