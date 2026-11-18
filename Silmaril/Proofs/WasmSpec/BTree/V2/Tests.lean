module

public import Silmaril.WasmSpec.BTree.V2.Defs
public import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public import Silmaril.Wasm.Logic.Words.Thms
public import Silmaril.Wasm.Verify.Refute.Defs
public import Silmaril.Wasm.Binaryen.Exe.Encode
public meta import Silmaril.WasmSpec.BTree.V2.Defs
public meta import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
public meta import Silmaril.Wasm.Logic.Words.Thms
public meta import Silmaril.Wasm.Verify.Refute.Defs
public meta import Silmaril.Wasm.Binaryen.Exe.Encode

@[expose] public section

/-!
# The B-tree library, version 2: tests

**Executed** (`#guard`, not a proof), with silmaril-lean's verified interpreter on the
instantiated module: `btree_create` on the empty memory, then `btree_insert` of a sequence of
keys with branching factor `2` (several splits and a root split), then `btree_search` of
every key from `-2` to `21`; `btree_create` and `btree_insert` when every `memory.grow`
fails. The property tests (random insert/search sequences against a Rust `BTreeSet` and a
model of CLRS insertion, B-tree checks of the memory after every insertion, the memory frame,
out-of-memory runs and free pages) run on `wasmi` (`tools/wasm-spec-fuzz`, `cargo test`)
against `wasmBytes`, the encoding of `program` checked below.

A Silmaril addition.
-/

namespace Silmaril.WasmSpec.BTree.V2

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Words Silmaril.Wasm.Verify

/-- Call function `j` on `args` in `s`, with `memory.grow` failing iff `fail`: the store after
the call and its result. -/
def runS (fail : Bool) (s : Store Nat) (j : Nat) (args : List Val) : Option (Store Nat × Result) :=
  match Silmaril.Wasm.SingleThreaded.Exec.runInvoke? (fun _ _ _ _ => fail) refFuel s j args with
  | some (c, _, some r) => some (c.store, r)
  | _ => none

/-- `btree_create 2`, then `btree_insert` of each key; `none` unless every call returns `1`. -/
def build (keys : List Int) : Option (Store Nat) := do
  let (s, r) ← runS false store₀ 8 [.i32 2]
  if r != .values [.i32 1] then none
  keys.foldlM (fun s k => do
    let (s, r) ← runS false s 9 [.i32 (BitVec.ofInt 32 k)]
    if r == .values [.i32 1] then some s else none) s

/-- The keys inserted. -/
def keys : List Int := [10, 3, 17, 5, 1, 12, 8, 20, 15, 7, 0, 19, 11, 3, 10, 14]

/-- Whether `btree_search k` returns `b` after `build keys`. -/
def searches (k : Int) (b : Nat) : Bool :=
  match build keys with
  | some s => (runS false s 2 [.i32 (BitVec.ofInt 32 k)]).map Prod.snd ==
      some (.values [.i32 (BitVec.ofNat 32 b)])
  | none => false

#guard (List.range 24).all fun n =>
  let k : Int := n - 2
  searches k (if keys.contains k then 1 else 0)

-- With growth failing, `btree_create` returns `0`.
#guard (runS true store₀ 8 [.i32 2]).map Prod.snd == some (.values [.i32 0])

-- With growth failing after a full root leaf (three keys, `t = 2`), `btree_insert` of a new
-- key returns `0`, and every old key is still found.
#guard match build [1, 2, 3] with
  | some s => match runS true s 9 [.i32 4] with
    | some (s', r) => r == .values [.i32 0] && [1, 2, 3].all (fun k =>
        (runS false s' 2 [.i32 k]).map Prod.snd == some (.values [.i32 1])) &&
        (runS false s' 2 [.i32 4]).map Prod.snd == some (.values [.i32 0])
    | none => false
  | none => false

/-- The binary encoding of `program` (silmaril-lean's `encodeModule?`), as run by the `wasmi`
property tests in `tools/wasm-spec-fuzz` (which check their `.wasm` file against this list). -/
def wasmBytes : List UInt8 := [
  0, 97, 115, 109, 1, 0, 0, 0, 1, 22, 4, 96, 2, 127, 127, 1, 127, 96, 1, 127, 1, 127, 96, 3, 127,
  127, 127, 0, 96, 0, 1, 127, 3, 11, 10, 0, 0, 1, 2, 2, 3, 2, 0, 1, 1, 5, 3, 1, 0, 0, 7, 142, 1,
  11, 6, 109, 101, 109, 111, 114, 121, 2, 0, 7, 111, 98, 97, 95, 103, 101, 116, 0, 0, 8, 111, 98,
  97, 95, 102, 105, 110, 100, 0, 1, 12, 98, 116, 114, 101, 101, 95, 115, 101, 97, 114, 99, 104, 0,
  2, 9, 98, 97, 95, 105, 110, 115, 101, 114, 116, 0, 3, 7, 98, 97, 95, 99, 111, 112, 121, 0, 4,
  10, 97, 108, 108, 111, 99, 95, 110, 111, 100, 101, 0, 5, 11, 115, 112, 108, 105, 116, 95, 99,
  104, 105, 108, 100, 0, 6, 14, 105, 110, 115, 101, 114, 116, 95, 110, 111, 110, 102, 117, 108,
  108, 0, 7, 12, 98, 116, 114, 101, 101, 95, 99, 114, 101, 97, 116, 101, 0, 8, 12, 98, 116, 114,
  101, 101, 95, 105, 110, 115, 101, 114, 116, 0, 9, 10, 241, 6, 10, 13, 0, 32, 0, 32, 1, 65, 4,
  108, 106, 40, 2, 4, 11, 47, 1, 1, 127, 2, 64, 3, 64, 32, 2, 32, 0, 40, 2, 0, 79, 13, 1, 32, 0,
  32, 2, 65, 4, 108, 106, 40, 2, 4, 32, 1, 78, 13, 1, 32, 2, 65, 1, 106, 33, 2, 12, 0, 11, 11, 32,
  2, 11, 101, 1, 3, 127, 65, 4, 40, 2, 0, 33, 1, 2, 64, 3, 64, 32, 1, 65, 128, 128, 4, 108, 65, 4,
  106, 33, 3, 32, 3, 32, 0, 16, 1, 33, 2, 32, 2, 32, 3, 40, 2, 0, 73, 4, 64, 32, 3, 32, 2, 16, 0,
  32, 0, 70, 4, 64, 65, 1, 15, 11, 11, 32, 1, 65, 128, 128, 4, 108, 40, 2, 0, 4, 64, 65, 0, 15,
  11, 32, 1, 65, 128, 128, 4, 108, 65, 128, 128, 2, 106, 32, 2, 16, 0, 33, 1, 12, 0, 11, 11, 65,
  0, 11, 81, 1, 1, 127, 32, 0, 40, 2, 0, 33, 3, 2, 64, 3, 64, 32, 3, 32, 1, 77, 13, 1, 32, 0, 32,
  3, 65, 4, 108, 106, 32, 0, 32, 3, 65, 4, 108, 106, 40, 2, 0, 54, 2, 4, 32, 3, 65, 1, 107, 33, 3,
  12, 0, 11, 11, 32, 0, 32, 1, 65, 4, 108, 106, 32, 2, 54, 2, 4, 32, 0, 32, 0, 40, 2, 0, 65, 1,
  106, 54, 2, 0, 11, 55, 1, 1, 127, 2, 64, 3, 64, 32, 3, 32, 2, 79, 13, 1, 32, 1, 32, 3, 65, 4,
  108, 106, 32, 0, 32, 3, 65, 4, 108, 106, 40, 2, 0, 54, 2, 4, 32, 3, 65, 1, 106, 33, 3, 12, 0,
  11, 11, 32, 1, 32, 2, 54, 2, 0, 11, 60, 1, 2, 127, 65, 8, 40, 2, 0, 33, 0, 32, 0, 4, 64, 32, 0,
  65, 1, 107, 33, 0, 65, 8, 32, 0, 54, 2, 0, 32, 0, 65, 4, 108, 40, 2, 12, 15, 11, 65, 1, 64, 0,
  33, 1, 32, 1, 65, 128, 128, 2, 79, 4, 64, 65, 127, 15, 11, 32, 1, 11, 169, 1, 1, 4, 127, 65, 0,
  40, 2, 0, 33, 3, 32, 0, 65, 128, 128, 4, 108, 33, 4, 32, 4, 65, 128, 128, 2, 106, 32, 1, 16, 0,
  65, 128, 128, 4, 108, 33, 5, 32, 2, 65, 128, 128, 4, 108, 33, 6, 32, 6, 32, 5, 40, 2, 0, 54, 2,
  0, 32, 5, 65, 8, 106, 32, 3, 65, 4, 108, 106, 32, 6, 65, 4, 106, 32, 3, 65, 1, 107, 16, 4, 32,
  5, 40, 2, 0, 69, 4, 64, 32, 5, 65, 132, 128, 2, 106, 32, 3, 65, 4, 108, 106, 32, 6, 65, 128,
  128, 2, 106, 32, 3, 16, 4, 32, 5, 32, 3, 54, 2, 128, 128, 2, 11, 32, 4, 65, 4, 106, 32, 1, 32,
  5, 65, 4, 106, 32, 3, 65, 1, 107, 16, 0, 16, 3, 32, 5, 32, 3, 65, 1, 107, 54, 2, 4, 32, 4, 65,
  128, 128, 2, 106, 32, 1, 65, 1, 106, 32, 2, 16, 3, 11, 132, 1, 1, 4, 127, 32, 0, 65, 128, 128,
  4, 108, 33, 2, 32, 2, 65, 4, 106, 32, 1, 16, 1, 33, 3, 32, 2, 40, 2, 0, 4, 64, 32, 2, 65, 4,
  106, 32, 3, 32, 1, 16, 3, 65, 1, 15, 11, 32, 2, 65, 128, 128, 2, 106, 32, 3, 16, 0, 33, 4, 32,
  4, 65, 128, 128, 4, 108, 40, 2, 4, 65, 0, 40, 2, 0, 65, 2, 108, 65, 1, 107, 70, 4, 64, 16, 5,
  33, 5, 32, 5, 65, 127, 70, 4, 64, 65, 0, 15, 11, 32, 0, 32, 3, 32, 5, 16, 6, 32, 1, 32, 2, 65,
  4, 106, 32, 3, 16, 0, 74, 4, 64, 32, 5, 33, 4, 11, 11, 32, 4, 32, 1, 16, 7, 11, 56, 0, 65, 2,
  64, 0, 65, 127, 70, 4, 64, 65, 0, 15, 11, 65, 0, 32, 0, 54, 2, 0, 65, 4, 65, 1, 54, 2, 0, 65, 8,
  65, 0, 54, 2, 0, 65, 128, 128, 4, 65, 1, 54, 2, 0, 65, 132, 128, 4, 65, 0, 54, 2, 0, 65, 1, 11,
  153, 1, 1, 3, 127, 32, 0, 16, 2, 4, 64, 65, 1, 15, 11, 65, 4, 40, 2, 0, 33, 1, 32, 1, 65, 128,
  128, 4, 108, 40, 2, 4, 65, 0, 40, 2, 0, 65, 2, 108, 65, 1, 107, 70, 4, 64, 16, 5, 33, 2, 32, 2,
  65, 127, 70, 4, 64, 65, 0, 15, 11, 16, 5, 33, 3, 32, 3, 65, 127, 70, 4, 64, 65, 0, 15, 11, 32,
  2, 65, 128, 128, 4, 108, 65, 0, 54, 2, 0, 32, 2, 65, 128, 128, 4, 108, 65, 0, 54, 2, 4, 32, 2,
  65, 128, 128, 4, 108, 65, 1, 54, 2, 128, 128, 2, 32, 2, 65, 128, 128, 4, 108, 32, 1, 54, 2, 132,
  128, 2, 32, 2, 65, 0, 32, 3, 16, 6, 65, 4, 32, 2, 54, 2, 0, 32, 2, 33, 1, 11, 32, 1, 32, 0, 16,
  7, 11]

#guard (Silmaril.Wasm.Binaryen.Exe.encodeModule? program).toOption == some wasmBytes

end Silmaril.WasmSpec.BTree.V2
