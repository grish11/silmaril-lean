module

public import Silmaril.WasmSpec.BTree.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Verify.Refute.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public meta import Silmaril.WasmSpec.BTree.Defs
public meta import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public meta import Silmaril.Wasm.Logic.Words.Thms
public meta import Silmaril.Wasm.Verify.Refute.Defs
public meta import Silmaril.Wasm.Binaryen.Exe.Encode

@[expose] public section

/-!
# The B-tree library: tests

**Executed** (`#guard`, not a proof): `oba_find` and `oba_get` of the instantiated module run
with silmaril-lean's verified interpreter on an ordered array, and `btree_search` on a
two-level tree laid out by hand (root page `1` with key `10`, leaf pages `2` and `3`) in a
memory of four pages. The property tests (random B-trees built by CLRS insertion, 300 trees,
every key from `-210` to `209`) run on `wasmi` (`tools/wasm-spec-fuzz`, `cargo test`) against
`wasmBytes`, the encoding of `program` checked below.

A Silmaril addition.
-/

namespace Silmaril.WasmSpec.BTree

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words Silmaril.Wasm.Verify

/-- The store with memory `0` replaced by `bytes` (same type). -/
def storeWith (bytes : ByteArray) : Store Nat :=
  match store₀.mems with
  | mi :: rest => { store₀ with mems := { mi with bytes := bytes } :: rest }
  | [] => store₀

/-- Call function `j` on `args`. -/
def run (bytes : ByteArray) (j : Nat) (args : List Val) : Option Result :=
  match Silmaril.Wasm.SingleThreaded.Exec.runInvoke? refOracle refFuel (storeWith bytes) j args with
  | some (_, _, r) => r
  | none => none

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- An OBA `[-3, 1, 4, 9]` at `100`. -/
def obaMem : ByteArray := writeWords (zeros 65536) 100 [4, BitVec.ofInt 32 (-3), 1, 4, 9]

#guard run obaMem 1 [.i32 100, .i32 4] == some (.values [.i32 2])
#guard run obaMem 1 [.i32 100, .i32 (BitVec.ofInt 32 (-10))] == some (.values [.i32 0])
#guard run obaMem 1 [.i32 100, .i32 10] == some (.values [.i32 4])
#guard run obaMem 0 [.i32 100, .i32 3] == some (.values [.i32 9])

/-- A B-tree with `t = 2`: root page `1` (key `10`), leaves page `2` (keys `3, 7`) and page `3`
(key `20`). -/
def treeMem : ByteArray :=
  let B := writeWords (zeros (4 * 65536)) 0 [2, 1]
  let B := writeWords B (65536 * 1) [0, 1, 10]
  let B := writeWords B (65536 * 1 + 32768) [2, 2, 3]
  let B := writeWords B (65536 * 2) [1, 2, 3, 7]
  writeWords B (65536 * 3) [1, 1, 20]

#guard [3, 7, 10, 20].all fun k => run treeMem 2 [.i32 k] == some (.values [.i32 1])
#guard [0, 4, 11, 21].all fun k => run treeMem 2 [.i32 k] == some (.values [.i32 0])

/-- The binary encoding of `program` (silmaril-lean's `encodeModule?`), as run by the `wasmi`
property tests in `tools/wasm-spec-fuzz` (which check their `.wasm` file against this list). -/
def wasmBytes : List UInt8 := [
  0, 97, 115, 109, 1, 0, 0, 0, 1, 12, 2, 96, 2, 127, 127, 1, 127, 96, 1, 127, 1, 127, 3, 4, 3,
  0, 0, 1, 5, 3, 1, 0, 1, 7, 46, 4, 6, 109, 101, 109, 111, 114, 121, 2, 0, 7, 111, 98, 97, 95,
  103, 101, 116, 0, 0, 8, 111, 98, 97, 95, 102, 105, 110, 100, 0, 1, 12, 98, 116, 114, 101, 101,
  95, 115, 101, 97, 114, 99, 104, 0, 2, 10, 165, 1, 3, 13, 0, 32, 0, 32, 1, 65, 4, 108, 106, 40,
  2, 4, 11, 47, 1, 1, 127, 2, 64, 3, 64, 32, 2, 32, 0, 40, 2, 0, 79, 13, 1, 32, 0, 32, 2, 65, 4,
  108, 106, 40, 2, 4, 32, 1, 78, 13, 1, 32, 2, 65, 1, 106, 33, 2, 12, 0, 11, 11, 32, 2, 11, 101,
  1, 3, 127, 65, 4, 40, 2, 0, 33, 1, 2, 64, 3, 64, 32, 1, 65, 128, 128, 4, 108, 65, 4, 106, 33,
  3, 32, 3, 32, 0, 16, 1, 33, 2, 32, 2, 32, 3, 40, 2, 0, 73, 4, 64, 32, 3, 32, 2, 16, 0, 32, 0,
  70, 4, 64, 65, 1, 15, 11, 11, 32, 1, 65, 128, 128, 4, 108, 40, 2, 0, 4, 64, 65, 0, 15, 11, 32,
  1, 65, 128, 128, 4, 108, 65, 128, 128, 2, 106, 32, 2, 16, 0, 33, 1, 12, 0, 11, 11, 65, 0, 11]

#guard (Silmaril.Wasm.Binaryen.Exe.encodeModule? program).toOption == some wasmBytes

end Silmaril.WasmSpec.BTree
