module

public import Silmaril.Wasm.Examples.Farkas.Defs
public import Silmaril.Wasm.Examples.LRAT.Defs
public import Silmaril.Wasm.Logic.Words.Defs
public import Silmaril.Logic.LinArith.Carrier.Defs
public import Silmaril.Wasm.Verify.Checker.Defs
public import Silmaril.Wasm.Acceptor.Alloc.Defs
public import Silmaril.Wasm.Acceptor.Code.Defs

/-!
# The Farkas acceptor as a core Wasm module: definitions

`prog` is a Core 3.0 module (two memories) meant to be wrapped as a component whose export takes
its lists through the canonical ABI (`(canon lift … (memory 0) (realloc …))`, the component's
memory `0` being the core export `memory`), at the typed interface of
`Silmaril.Logic.LinArith.Carrier`:

```wit
record ineq { coeffs: list<tuple<u32, s64>>, bound: s64 }
check: func(system: list<ineq>, y: list<s64>) -> bool
```

| export | type | meaning |
|---|---|---|
| `memory` | memory `1`, 16 pages (1 MiB), maximum 16 | the canonical-ABI memory |
| `cabi_realloc(old, old_size, align, new_size) -> ptr` | `[i32 i32 i32 i32] → [i32]` | bump allocator |
| `check(sp, sl, yp, yl) -> i32` | `[i32 i32 i32 i32] → [i32]` | the `sl` inequalities at `sp`, with the `yl` multipliers at `yp` |

**The canonical-ABI layout** of the arguments: `list<ineq>` is a pointer and a length; each
`ineq` takes 16 bytes (alignment 8): the `coeffs` list as a pointer (`i32` at `+0`) and a length
(`i32` at `+4`), then `bound: s64` at `+8`. Each `tuple<u32, s64>` takes 16 bytes (alignment
8): the `u32` at `+0`, the `s64` at `+8`. `list<s64>` is 8 bytes per element.

**The module** extends the streaming Farkas checker `Silmaril.Wasm.Examples.Farkas.farkasMod`:
its three functions (`row`, `entry`, `check`) keep the indices `0 … 2` and their bodies, its
four globals the indices `0 … 3` and its one-page memory the index `0`; none of them is
exported. Added are the global `4` (the heap pointer `top`), the memory `1` (the canonical-ABI
memory) and the functions `3` (`cabi_realloc`) and `4` (`check`). The checker's functions only
use memory `0` and globals `0 … 3`; the new code only reads memory `1` and writes global `4`.

**The allocator** is the acceptor kit's `Silmaril.Wasm.Acceptor.reallocFunc` (shared with
`SatAccept` and `LratAccept`), on global `4` and the `memBytes` of memory `1`: it returns
`p = align_up(top, align)` and sets `top := p + new_size` when `top ≤ p ≤ memBytes` and
`new_size ≤ memBytes - p`; otherwise it sets `top := memBytes` and returns `memBytes`. It never
traps and never lowers `top`. The check resets `top` to `heapBase` before returning.

**The check** first **resets** the checker by calling its `check()` and dropping the answer:
that scan zeroes every accumulator slot and resets the four globals, so every call starts from
the state of a fresh instance and repeated calls are independent. If `yl ≠ sl` the answer is
`0`. Otherwise, for each inequality `i < sl` in order, it calls `row(y_i, bound_i)` and then
`entry(j, a)` for each coefficient pair `(j, a)` of the inequality in order, and answers
`check()`.

The checker's bounds apply (`|y|, |b|, |a| ≤ 2³⁰`, `y ≥ 0`, variables `j < 8192`, accumulators
within `2⁶²`): out-of-range input sets the checker's sticky flag, which can only make the answer
`0`. So the acceptor is sound for every input and complete only within the bounds. The checker
prepends rows and coefficients (`Cmd.apply`), so the rows it loads are the inequalities in
reverse order, each with its coefficients reversed; this changes no sum.

New code (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.FarkasAccept

open Silmaril.Wasm Silmaril.Wasm.Examples.Farkas
open Silmaril.Wasm.Examples.LRAT (c32 lget lset gget gset iadd isub imul iand ieq ine igeu iltu
  ieqz ifThen)

/-- The ABI memory size in bytes (16 pages). -/
abbrev memBytes : Nat := 1048576

/-- The initial (and reset) value of the heap pointer. -/
abbrev heapBase : Nat := 16

/-- The heap-pointer global. -/
abbrev gHeap : Nat := 4

/-! ## Instruction shorthands -/

/-- `i32.load` from memory `1` (the ABI memory) at offset `0`. -/
abbrev ld1 : Instr := .intLoad .i32 none ⟨1⟩ ⟨2, 0⟩

/-- `i64.load` from memory `1` (the ABI memory) at offset `0`. -/
abbrev ld64 : Instr := .intLoad .i64 none ⟨1⟩ ⟨3, 0⟩

/-- `call j` (`Silmaril.Wasm.Acceptor.callf`). -/
abbrev callf (j : Nat) : Instr := Silmaril.Wasm.Acceptor.callf j

/-! ## The allocator -/

/-- `cabi_realloc(old, osz, al, nsz)`: the kit's allocator on global `gHeap` for `memBytes`
bytes. -/
abbrev reallocFunc : Func := Silmaril.Wasm.Acceptor.reallocFunc ⟨3⟩ gHeap memBytes

/-! ## The check

Locals: `0` `sp`, `1` `sl`, `2` `yp`, `3` `yl`; `4` the inequality index `i`, `5` the
coefficient pointer `cp` of inequality `i`, `6` its length `cl`, `7` the coefficient index `k`,
`8` the answer. -/

/-- One coefficient pair: leave when `k = cl`; else `entry(j, a)` for the pair `(j, a)` at
`cp + 16 k`, `k += 1`. -/
def entryLoopBody : List Instr :=
  [lget 7, lget 6, igeu, .brIf ⟨1⟩,
    lget 5, lget 7, c32 16, imul, iadd, ld1,
    lget 5, lget 7, c32 16, imul, iadd, c32 8, iadd, ld64,
    callf 1,
    lget 7, c32 1, iadd, lset 7, .br ⟨0⟩]

/-- One inequality: leave when `i = sl`; else `row(y_i, bound_i)` for the multiplier at
`yp + 8 i` and the bound at `sp + 16 i + 8`, read `(cp, cl)` at `sp + 16 i`, feed the pairs,
`i += 1`. -/
def rowLoopBody : List Instr :=
  [lget 4, lget 1, igeu, .brIf ⟨1⟩,
    lget 2, lget 4, c32 8, imul, iadd, ld64,
    lget 0, lget 4, c32 16, imul, iadd, c32 8, iadd, ld64,
    callf 0,
    lget 0, lget 4, c32 16, imul, iadd, ld1, lset 5,
    lget 0, lget 4, c32 16, imul, iadd, c32 4, iadd, ld1, lset 6,
    c32 0, lset 7, .block .empty [.loop .empty entryLoopBody],
    lget 4, c32 1, iadd, lset 4, .br ⟨0⟩]

/-- The feeding and the answer, when `yl = sl`. -/
def feedCode : List Instr :=
  [c32 0, lset 4, .block .empty [.loop .empty rowLoopBody], callf 2, lset 8]

/-- `check(sp, sl, yp, yl)`: reset the checker (`check()`, answer dropped), answer `0` unless
`yl = sl`, else feed the system and answer `check()`; then `top := heapBase`. -/
def checkBody : List Instr :=
  [callf 2, .drop, lget 3, lget 1, ieq, ifThen feedCode,
    c32 heapBase, gset gHeap, lget 8]

/-! ## The module -/

/-- `[i32 i32 i32 i32] → [i32]`. -/
def ty4 : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32, .i32, .i32], [.i32]⟩⟩]⟩

/-- The locals of the check (after the four parameters): five `i32`s. -/
def checkLocals : List ValType := List.replicate 5 .i32

/-- The ABI memory's type: 16 pages, not growable. -/
def accMt : MemoryType := ⟨.i32, ⟨16, some 16⟩⟩

/-- **The Farkas acceptor module**: `farkasMod`, extended. -/
def prog : Module where
  types := farkasMod.types ++ [ty4]
  globals := farkasMod.globals ++ [⟨⟨.var, .i32⟩, [c32 heapBase]⟩]
  memories := farkasMod.memories ++ [accMt]
  funcs := farkasMod.funcs ++ [
    reallocFunc,
    ⟨⟨3⟩, checkLocals, checkBody⟩]
  exports := [⟨"memory", .memory ⟨1⟩⟩, ⟨"cabi_realloc", .func ⟨3⟩⟩, ⟨"check", .func ⟨4⟩⟩]

/-! ## What the check reads -/

open Silmaril.Logic.LinArith.Carrier

/-- The little-endian 64-bit word at byte `a` (`0` out of bounds). -/
def dw (B : ByteArray) (a : Nat) : BitVec 64 := (Silmaril.Wasm.Execution.Memory.load B a 8).getD 0

/-- The `n` 64-bit words at byte `p`: a `list<s64>` value. -/
def wordsAt64 (B : ByteArray) (p n : Nat) : List S64 := (List.range n).map fun i => dw B (p + 8 * i)

/-- The `n` coefficient pairs at byte `p`: a `list<tuple<u32, s64>>` value. -/
def coeffsAt (B : ByteArray) (p n : Nat) : List (U32 × S64) :=
  (List.range n).map fun k =>
    (Silmaril.Wasm.Logic.Words.wd B (p + 16 * k), dw B (p + 16 * k + 8))

/-- The inequality record at byte `a`. -/
def ineqAt (B : ByteArray) (a : Nat) : IneqW :=
  ⟨coeffsAt B (Silmaril.Wasm.Logic.Words.wd B a).toNat (Silmaril.Wasm.Logic.Words.wd B (a + 4)).toNat,
    dw B (a + 8)⟩

/-- **The system** of `n` inequality records at byte `p`: a `list<ineq>` value. -/
def systemAt (B : ByteArray) (p n : Nat) : SystemW := (List.range n).map fun i => ineqAt B (p + 16 * i)

/-- Every record and every coefficient list of the system lies in memory. -/
def IneqsIn (B : ByteArray) (p n : Nat) : Prop :=
  p + 16 * n ≤ B.size ∧ ∀ i < n,
    (Silmaril.Wasm.Logic.Words.wd B (p + 16 * i)).toNat +
      16 * (Silmaril.Wasm.Logic.Words.wd B (p + 16 * i + 4)).toNat ≤ B.size

/-! ## The instance, and the stores the theorems are about -/

section Inst

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- The instantiated acceptor (`Silmaril.Wasm.Verify.instOf`: validated, instantiated against
no imports). -/
def accI : ScalarInstance := Silmaril.Wasm.Verify.instOf prog

/-- Its store. -/
def accS : Store Nat := accI.store

/-! The elaborator never computes the instance: every fact about it is a kernel check
(`Silmaril.Proofs.Wasm.Examples.FarkasAccept.Inst`). -/
attribute [irreducible] accI accS

/-- The type of the `i32` globals (mutable `i32`). -/
def accG32 : CGlobalType := ⟨.var, .num (.int .i32)⟩

/-- The type of the `i64` globals (mutable `i64`). -/
def accG64 : CGlobalType := ⟨.var, .num (.int .i64)⟩

/-- The type of the checker's memory (memory `0`). -/
def farkasMemType : MemoryType := ⟨.i32, ⟨1, some 1⟩⟩

/-- **The stores of the acceptor**: the instance's functions, any checker state (the four
globals `bad`, `hasRow`, `y`, `accB` and the 64 KiB memory `B₀`), the heap pointer `top`
(global `4`) and the 1 MiB ABI memory `B₁` (memory `1`). The instantiated store is one (zero
globals and memories, `top = 16`); a call of an export or a write of the embedder into the ABI
memory leads to another. -/
structure AccStore (s : Store Nat) (top : BitVec 32) (B₁ : ByteArray) : Prop where
  funcs : s.funcs = accS.funcs
  globals : ∃ (bad hr : BitVec 32) (y vb : BitVec 64), s.globals =
    [⟨accG32, Val.i32 bad⟩, ⟨accG32, Val.i32 hr⟩, ⟨accG64, Val.i64 y⟩, ⟨accG64, Val.i64 vb⟩,
      ⟨accG32, Val.i32 top⟩]
  mems : ∃ B₀ : ByteArray, B₀.size = 65536 ∧ s.mems = [⟨farkasMemType, B₀⟩, ⟨accMt, B₁⟩]
  size₁ : B₁.size = memBytes

end Inst

/-! ## The allocator's contract -/

/-- What a call of `cabi_realloc(old, osz, al, nsz)` does when the heap pointer is `top`
(`Silmaril.Wasm.Acceptor.ReallocOk` at `memBytes`): it answers `r` and sets the heap pointer to
`t'`, never lower and within memory; either the block `[r, r + nsz)` is fresh
(`r = align_up(top, al) ≥ top`, `t' = r + nsz`) or the allocation failed (`r = t' = memBytes`). -/
abbrev ReallocOk (top al nsz r t' : BitVec 32) : Prop :=
  Silmaril.Wasm.Acceptor.ReallocOk memBytes top al nsz r t'

end Silmaril.Wasm.Examples.FarkasAccept
