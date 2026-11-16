module

public import Silmaril.WasmSpec.IsSorted.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Verify.Refute.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public meta import Silmaril.WasmSpec.IsSorted.Defs
public meta import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public meta import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public meta import Silmaril.Wasm.Logic.Words.Thms
public meta import Silmaril.Wasm.Verify.Refute.Defs
public meta import Silmaril.Wasm.Binaryen.Exe.Encode

@[expose] public section

/-!
# `is_sorted`: tests

**Executed** (`#guard`, not a proof): the instantiated module is run with silmaril-lean's
verified interpreter (`Silmaril.Wasm.SingleThreaded.Exec.runInvoke?`, whose runs are Core runs)
on arrays written into its memory, and the answer is compared with the specification's
`answer` (a property test over 300 pseudo-random arrays, plus sorted and edge cases). A larger
property test runs on `wasmi` (`tools/wasm-spec-fuzz`, `cargo test`) against `wasmBytes`, the
encoding of `program` checked below.

A Silmaril addition.
-/

namespace Silmaril.WasmSpec.IsSorted

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words Silmaril.Wasm.Verify

/-- The store with the words `xs` at `p` in memory `0`. -/
def storeWith (p : Nat) (xs : List (BitVec 32)) : Store Nat :=
  match store₀.mems with
  | mi :: rest => { store₀ with mems := { mi with bytes := writeWords mi.bytes p xs } :: rest }
  | [] => store₀

/-- Run `is_sorted(p, |xs|)` on the array `xs` at `p`. -/
def run (p : Nat) (xs : List (BitVec 32)) : Option Result :=
  match Silmaril.Wasm.SingleThreaded.Exec.runInvoke? refOracle refFuel (storeWith p xs) 0
      [.i32 (BitVec.ofNat 32 p), .i32 (BitVec.ofNat 32 xs.length)] with
  | some (_, _, r) => r
  | none => none

/-- The run agrees with the specification. -/
def agrees (p : Nat) (xs : List (BitVec 32)) : Bool :=
  run p xs == some (.values [.i32 (answer xs)])

/-- A linear congruential generator. -/
def lcg (x : Nat) : Nat := (1103515245 * x + 12345) % 2 ^ 31

/-- `k` pseudo-random words in `[-r, r)` from the seed `x`. -/
def randWords (x r : Nat) : Nat → List (BitVec 32)
  | 0 => []
  | k + 1 => BitVec.ofInt 32 ((lcg x % (2 * r) : Nat) - (r : Int)) :: randWords (lcg x) r k

/-- The `j`-th random array: length `j % 9`, values in a range that makes sorted arrays common
for small lengths. -/
def randArray (j : Nat) : List (BitVec 32) := randWords (j * 7919 + 1) (1 + j % 5) (j % 9)

#guard agrees 16 []
#guard agrees 16 [5]
#guard agrees 16 [1, 2, 2, 3]
#guard agrees 16 [3, 2]
#guard agrees 100 [BitVec.ofInt 32 (-5), 0, 7, 0x7fffffff]
#guard agrees 100 [0x7fffffff, BitVec.ofInt 32 (-1)]
#guard run 16 [1, 2, 3] == some (.values [.i32 1])
#guard run 16 [1, 3, 2] == some (.values [.i32 0])
#guard (List.range 300).all fun j => agrees (4 * (j % 50)) (randArray j)
#guard (List.range 100).all fun j =>
  agrees 64 ((randArray j).mergeSort fun x y => decide (x.toInt ≤ y.toInt))

/-- The binary encoding of `program` (silmaril-lean's `encodeModule?`), as run by the `wasmi`
property tests in `tools/wasm-spec-fuzz` (which check their `.wasm` file against this list). -/
def wasmBytes : List UInt8 := [
  0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 127, 127, 1, 127, 3, 2, 1, 0, 5, 3, 1, 0, 1, 7,
  22, 2, 6, 109, 101, 109, 111, 114, 121, 2, 0, 9, 105, 115, 95, 115, 111, 114, 116, 101, 100,
  0, 0, 10, 65, 1, 63, 1, 1, 127, 65, 1, 33, 2, 2, 64, 3, 64, 32, 2, 32, 1, 79, 13, 1, 32, 0,
  32, 2, 65, 1, 107, 65, 4, 108, 106, 40, 2, 0, 32, 0, 32, 2, 65, 4, 108, 106, 40, 2, 0, 74, 13,
  1, 32, 2, 65, 1, 106, 33, 2, 12, 0, 11, 11, 32, 2, 32, 1, 79, 11]

#guard (Silmaril.Wasm.Binaryen.Exe.encodeModule? program).toOption == some wasmBytes

end Silmaril.WasmSpec.IsSorted
