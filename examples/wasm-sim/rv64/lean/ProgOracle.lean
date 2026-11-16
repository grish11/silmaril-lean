/-
Whole-program oracle: runs `Silmaril.RiscV.Ext.MState.step` (Lean RV64 model)
from an ELF image until the first non-retired outcome or a step limit, for
differential testing of the Wasm simulators (`wasm-sim-rv lean-prog <elf>`).

Input (stdin): first line `<entry> <limit>`; then one line per PT_LOAD segment
`<base> <memsz> <r> <w> <x> <hex bytes of the file image>` (rest zero).
All registers start at 0. Output: `<steps> <outcome> <pc> <x1> ... <x31> <fnv>`
where outcome is R (limit reached), S, F, U, TM, DM, DF as in StepOracle.lean
and fnv is FNV-1a-64 over the bytes of all segments in input order.
-/
import Silmaril.Machine.RiscV.Ext.Machine.Defs

open Silmaril Silmaril.RiscV Silmaril.RiscV.Ext Silmaril.Process

def hexByte (c1 c2 : Char) : Process.Byte :=
  let d (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  BitVec.ofNat 8 (16 * d c1 + d c2)

def parseHex : List Char → List Process.Byte
  | c1 :: c2 :: rest => hexByte c1 c2 :: parseHex rest
  | _ => []

/-- Rebuild the register file as a table lookup, so long runs do not chain closures. -/
def normalize (s : State) : State :=
  let arr := (List.range 32).toArray.map fun i => s.regs (BitVec.ofNat 5 i)
  { regs := fun r => arr.getD r.toNat 0, pc := s.pc }

def outcomeTag : Outcome → String
  | .retired _ => "R" | .stopped => "S" | .fetchFault => "F" | .undecodable _ => "U"
  | .targetMisaligned _ _ => "TM" | .dataMisaligned _ _ => "DM" | .dataFault _ _ => "DF"

def run (m : MState) : Nat → Nat → (Nat × String × MState)
  | 0, n => (n, "R", m)
  | fuel + 1, n =>
    match m.step with
    | .retired next => run { next with core := normalize next.core } fuel (n + 1)
    | o => (n, outcomeTag o, m)

def fnv (bytes : List Process.Byte) : Nat :=
  bytes.foldl (fun h b => ((h ^^^ b.toNat) * 0x100000001b3) % 2 ^ 64) 0xcbf29ce484222325

def main : IO Unit := do
  let stdin ← IO.getStdin
  let header := (← stdin.getLine).trimAsciiEnd.toString.splitOn " " |>.map String.toNat!
  let entry := header[0]!
  let limit := header[1]!
  let mut regions : List Region := []
  let mut bytes : ByteMemory := ∅
  let mut spans : List (Nat × Nat) := []
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let f := line.trimAsciiEnd.toString.splitOn " "
    if f.length < 5 then continue
    let base := f[0]!.toNat!
    let size := f[1]!.toNat!
    let image := parseHex (f.getD 5 "").toList
    regions := regions ++ [⟨base, size, ⟨f[2]! == "1", f[3]! == "1", f[4]! == "1"⟩⟩]
    bytes := Memory.install bytes base (image ++ List.replicate (size - image.length) 0)
    spans := spans ++ [(base, size)]
  let s0 : State := { regs := fun _ => 0, pc := BitVec.ofNat 64 entry }
  let (n, tag, m) := run ⟨s0, ⟨regions, bytes⟩⟩ limit 0
  let regs := (List.range 31).map fun i => toString (m.core.read (BitVec.ofNat 5 (i + 1))).toNat
  let all := spans.flatMap fun (b, sz) => (List.range sz).map fun k => m.memory.bytes.getD (b + k) 0
  IO.println s!"{n} {tag} {m.core.pc.toNat} {" ".intercalate regs} {fnv all}"
