import Silmaril.Compiler.Decompile.WordC.Defs

/-!
# A decompiled fixture: one straight-line block to C

    lake env lean --run tools/compiler-explorer/decompile_block.lean NAME HEXBYTES N IN1=REG,… OUT.json

Runs the repository's decompiler on the bytes of one block (no control transfer, `ret`
excluded): `SemLift.propose` (the untrusted proposer), `SemLift.check` (the checker the soundness
theorem `SemLift.check_sound` is about) on its proposal, and `WordC.regenerate` (the SSA
expression of `rax` as typed Ail and C source). It writes the C source and what produced it. It
states no theorem about the result.
-/

open Lean Silmaril.X86 Silmaril.X86.Decompile.SemLift Silmaril.Compiler.Decompile.WordC

def parseReg : String → Option Reg
  | "rdi" => some .rdi | "rsi" => some .rsi | "rdx" => some .rdx | "rcx" => some .rcx
  | "r8" => some .r8 | "r9" => some .r9 | _ => none

def hexByte (s : String) : Option (BitVec 8) :=
  (String.toNat? ("0x" ++ s)).map (BitVec.ofNat 8) <|>
    (if s.length == 2 then
      let v := s.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat
        else c.toLower.toNat - 'a'.toNat + 10)) 0
      some (BitVec.ofNat 8 v) else none)

def main (args : List String) : IO UInt32 := do
  let [name, hex, n, ins, out] := args
    | IO.eprintln "usage: NAME HEXBYTES N NAME=REG,… OUT"; return 2
  let some bytes := (hex.splitOn " ").filter (· ≠ "") |>.mapM hexByte
    | IO.eprintln "bad bytes"; return 2
  let some count := n.toNat? | return 2
  let some inputs := (ins.splitOn ",").mapM fun p => match p.splitOn "=" with
      | [v, r] => (parseReg r).map (·, v) | _ => none
    | IO.eprintln "bad inputs"; return 2
  let some summary := propose bytes count [.rax]
    | IO.eprintln "the proposer does not accept the block"; return 1
  let checked := check bytes count summary
  let some (_, expr) := summary.outs.head? | return 1
  match regenerate name inputs expr with
  | .error why => IO.eprintln s!"not regenerated: {why}"; return 1
  | .ok art =>
    IO.FS.writeFile out <| (Json.mkObj [
      ("source", Json.str art.source),
      ("checked", Json.bool checked),
      ("instructions", Json.num count),
      ("bytes", Json.str hex),
      ("lean_version", Json.str Lean.versionString),
      ("tool", Json.str "Silmaril.X86.Decompile.SemLift.propose, SemLift.check, Silmaril.Compiler.Decompile.WordC.regenerate")
    ]).pretty ++ "\n"
    return if checked then 0 else 1
