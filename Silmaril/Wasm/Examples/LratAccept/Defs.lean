module

public import Silmaril.Wasm.Examples.LRAT.Defs
public import Silmaril.Wasm.Logic.Words.Defs
public import Silmaril.Logic.SAT.Carrier.Defs
public import Silmaril.Wasm.Verify.Checker.Defs
public import Silmaril.Wasm.Acceptor.Alloc.Defs
public import Silmaril.Wasm.Acceptor.Code.Defs
public import Silmaril.Wasm.Acceptor.Abi.Defs

/-!
# The LRAT UNSAT acceptor as a core Wasm module: definitions

`prog` is a Core 3.0 module (two memories) meant to be wrapped as a component whose exports
take their lists through the canonical ABI (`(canon lift … (memory 0) (realloc …))`, the
component's memory `0` being the core export `memory`):

| export | type | meaning |
|---|---|---|
| `memory` | memory `1`, 16 pages (1 MiB), maximum 16 | the canonical-ABI memory |
| `cabi_realloc(old, old_size, align, new_size) -> ptr` | `[i32 i32 i32 i32] → [i32]` | bump allocator |
| `check-stream(pp, pl, cp, cl) -> i32` | `[i32 i32 i32 i32] → [i32]` | the stream problem `[pp, pp + 4 pl)` refuted by the certificate `[cp, cp + 4 cl)` |
| `check-nested(pp, pl, cp, cl) -> i32` | `[i32 i32 i32 i32] → [i32]` | the `pl` clauses `(ptr, len)` at `pp`, refuted by the certificate `[cp, cp + 4 cl)` |

**The module** extends the streaming LRAT checker `Silmaril.Wasm.Examples.LRAT.lratModule`:
its ten functions keep the indices `0 … 9` and their bodies, its eight globals the indices
`0 … 7` and its one-page memory the index `0`; none of them is exported. Added are the global
`8` (the heap pointer `top`), the memory `1` (the canonical-ABI memory) and the functions `10`
(`cabi_realloc`), `11` (`check-stream`) and `12` (`check-nested`). The LRAT functions only use
memory `0` and globals `0 … 7`; the new code only reads memory `1` and writes global `8`.

**The allocator** is the acceptor kit's `Silmaril.Wasm.Acceptor.reallocFunc` (shared with
`SatAccept` and `FarkasAccept`), on global `8` and the `memBytes` of memory `1`: it returns
`p = align_up(top, align)` and sets `top := p + new_size` when `top ≤ p ≤ memBytes` and
`new_size ≤ memBytes - p`; otherwise it sets `top := memBytes` and returns `memBytes`. It never
traps and never lowers `top`. Both checks reset `top` to `heapBase` before returning.

**The checks** first **reset** the LRAT state (`resetCode`: every word of memory `0` below the
arena is zeroed and the eight globals get their initial values), so every call starts from the
state of a fresh instance and repeated calls are independent. They then feed the problem to
`add_lit` (stream: every word; nested: every word of every clause, then `end_clause` per
clause) while checking that it is well formed (stream: no `Int32.MIN`, empty or last word `0`;
nested: no `0` or `Int32.MIN` inside a clause). On a well-formed problem the certificate is
parsed word by word by a state machine (`certCode`) following the flat LRAT stream format v1
(`Silmaril.Logic.SAT.Carrier.LratStream`), which drives `step_begin`, `step_lit`, `step_hint`,
`step_end`, `delete`, `rat_begin` and `rat_end`; any malformed word sends it to a sink state.
The answer is `1` when the problem is well formed, the certificate ends between steps, and
`unsat()` is nonzero; otherwise `0`.

The LRAT core's limits apply (clause ids below `1024`, literals `-1024 < x < 1024`, a 40 KiB
clause arena): out-of-range input is ignored or ends the input as the core documents, which can
only make the answer `0` (the soundness theorems hold for every input). A problem with an empty
input clause is refuted by the core as soon as it reads it, so it is accepted with any
well-formed certificate, including the empty one (the reference `lratStream`/`lratNested` asks
for an explicit empty-clause step).

New code (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Examples.LRAT

/-- The ABI memory size in bytes (16 pages). -/
abbrev memBytes : Nat := 1048576

/-- The initial (and reset) value of the heap pointer. -/
abbrev heapBase : Nat := 16

/-- The heap-pointer global. -/
abbrev gHeap : Nat := 8

/-! ## Instruction shorthands -/

/-- `i32.load` from memory `1` (the ABI memory) at offset `0`. -/
abbrev ld1 : Instr := .intLoad .i32 none ⟨1⟩ ⟨2, 0⟩

/-- `call j` (`Silmaril.Wasm.Acceptor.callf`). -/
abbrev callf (j : Nat) : Instr := Silmaril.Wasm.Acceptor.callf j

/-- `i32.const` of `Int32.MIN = 0x80000000`. -/
abbrev cMin : Instr := c32 2147483648

/-! ## The allocator -/

/-- `cabi_realloc(old, osz, al, nsz)`: the kit's allocator on global `gHeap` for `memBytes`
bytes. -/
abbrev reallocFunc : Func := Silmaril.Wasm.Acceptor.reallocFunc ⟨3⟩ gHeap memBytes

/-! ## Resetting the LRAT state -/

/-- Zero the words of memory `0` below the arena, `[0, arenaBase)`. Local `4` is the address. -/
def zeroLoopBody : List Instr :=
  [lget 4, c32 arenaBase, igeu, .brIf ⟨1⟩,
    lget 4, c32 0, istore,
    lget 4, c32 4, iadd, lset 4, .br ⟨0⟩]

/-- **The reset**: zero memory `0` below the arena and give the eight LRAT globals their initial
values (those of `lratModule`). -/
def resetCode : List Instr :=
  [c32 0, lset 4, .block .empty [.loop .empty zeroLoopBody],
    c32 0, gset gMode, c32 arenaBase, gset gTop, c32 arenaBase, gset gCstart, c32 0, gset gStamp,
    c32 0, gset gConfl, c32 0, gset gStepId, c32 0, gset gUnsat, c32 1, gset gNextId]

/-! ## Parsing the certificate

Locals: `2` `cp`, `4` the word index `j`, `5` the word `x`, `7` the state, `9` the next state,
`10` "`x` is positive" (`1 ≤ x < 2³¹`), `11` "`x` is a literal word", `12` the number of words
to read (`cl`, or `0` for a malformed problem).

States: `0` before a step (a tag); `1`, `5` the id of an addition (RUP) resp. RAT step; `2`,
`6` its literals; `3` the hints of an addition; `4` the ids of a deletion; `7` a RAT candidate
or the end of the groups; `8` the hints of a RAT group; `9` malformed (a sink). -/

/-- The classification of the word `x` (local `5`): local `10` "positive", local `11` "literal
word"; the next state (local `9`) defaults to the sink `9`. -/
def classifyCode : List Instr :=
  [lget 5, c32 1, isub, c32 2147483647, iltu, lset 10,
    lget 5, c32 0, ine, lget 5, cMin, ine, iand, lset 11,
    c32 9, lset 9]

/-- `if state = k then body`. -/
def guardOn (k : Nat) (body : List Instr) : List Instr := [lget 7, c32 k, ieq, ifThen body]

/-- State `0`: the tag `1` (addition), `2` (deletion) or `3` (RAT). -/
def tagBody : List Instr :=
  [lget 5, c32 1, ieq, ifThen [c32 1, lset 9],
    lget 5, c32 2, ieq, ifThen [c32 4, lset 9],
    lget 5, c32 3, ieq, ifThen [c32 5, lset 9]]

/-- States `1`, `5`: a positive id starts the step (`step_begin`), next state `next`. -/
def idBody (next : Nat) : List Instr :=
  [lget 10, ifThen [lget 5, callf 2, c32 next, lset 9]]

/-- States `2`, `6`: `0` ends the literals (next state `zeroNext`); a literal word goes to
`step_lit`. -/
def litsBody (zeroNext self : Nat) : List Instr :=
  [lget 5, ieqz, ifThen [c32 zeroNext, lset 9],
    lget 11, ifThen [lget 5, callf 3, c32 self, lset 9]]

/-- States `3`, `4`, `7`, `8`: `0` runs `zeroCode`; a positive word goes to function `j`. -/
def idsBody (zeroCode : List Instr) (j self : Nat) : List Instr :=
  [lget 5, ieqz, ifThen zeroCode,
    lget 10, ifThen [lget 5, callf j, c32 self, lset 9]]

/-- The dispatch on the state, for the word `x` in local `5`. -/
def dispatchCode : List Instr :=
  classifyCode ++
  guardOn 0 tagBody ++
  guardOn 1 (idBody 2) ++
  guardOn 5 (idBody 6) ++
  guardOn 2 (litsBody 3 2) ++
  guardOn 6 (litsBody 7 6) ++
  -- the hints of an addition; `0`: `step_end`
  guardOn 3 (idsBody [callf 5, c32 0, lset 9] 4 3) ++
  -- the ids of a deletion
  guardOn 4 (idsBody [c32 0, lset 9] 6 4) ++
  -- a RAT candidate (`rat_begin`); `0`: `rat_end`
  guardOn 7 (idsBody [callf 9, c32 0, lset 9] 8 8) ++
  -- the hints of a RAT group
  guardOn 8 (idsBody [c32 7, lset 9] 4 8) ++
  [lget 9, lset 7]

/-- One word of the certificate: leave when `j = n`, else read `x = cert[j]`, dispatch,
`j += 1`. -/
def certLoopBody : List Instr :=
  [lget 4, lget 12, igeu, .brIf ⟨1⟩,
    lget 2, lget 4, c32 4, imul, iadd, ld1, lset 5] ++
  dispatchCode ++
  [lget 4, c32 1, iadd, lset 4, .br ⟨0⟩]

/-- **The certificate and the answer.** Local `6` is "the problem is well formed"; the answer
goes to local `8`: `1` when the problem is well formed, the certificate ends in state `0` and
`unsat()` is nonzero. Then `top := heapBase` and the answer is returned. -/
def certCode : List Instr :=
  [lget 3, lget 6, imul, lset 12, c32 0, lset 4, c32 0, lset 7,
    .block .empty [.loop .empty certLoopBody],
    lget 6, lget 7, ieqz, iand, ifThen [callf 7, c32 0, ine, lset 8],
    c32 heapBase, gset gHeap, lget 8]

/-! ## The problem -/

/-- One word of a stream problem: leave when `i = pl`; else `add_lit(x)` for `x = problem[i]`,
`ok := ok ∧ x ≠ Int32.MIN`, `i += 1`. Locals: `0` `pp`, `1` `pl`, `4` `i`, `5` `x`, `6` `ok`. -/
def streamLoopBody : List Instr :=
  [lget 4, lget 1, igeu, .brIf ⟨1⟩,
    lget 0, lget 4, c32 4, imul, iadd, ld1, lset 5,
    lget 5, callf 0,
    lget 6, lget 5, cMin, ine, iand, lset 6,
    lget 4, c32 1, iadd, lset 4, .br ⟨0⟩]

/-- `check-stream(pp, pl, cp, cl)`. -/
def checkStreamBody : List Instr :=
  resetCode ++
  [c32 1, lset 6, c32 0, lset 4, .block .empty [.loop .empty streamLoopBody],
    -- terminated: empty, or the last word is 0
    lget 1, c32 0, ine, ifThen [lget 6, lget 0, lget 1, c32 4, imul, iadd, c32 4, isub, ld1,
      ieqz, iand, lset 6]] ++
  certCode

/-- One word of a clause of a nested problem: leave when `k = len`; else `add_lit(x)` for the
word `x` at `cpᵢ + 4k`, `ok := ok ∧ x` a literal word, `k += 1`. Locals: `5` `x`, `6` `ok`,
`13` `k`, `14` `cpᵢ`, `15` `len`. -/
def litLoopBody : List Instr :=
  [lget 13, lget 15, igeu, .brIf ⟨1⟩,
    lget 14, lget 13, c32 4, imul, iadd, ld1, lset 5,
    lget 5, callf 0,
    lget 6, lget 5, c32 0, ine, lget 5, cMin, ine, iand, iand, lset 6,
    lget 13, c32 1, iadd, lset 13, .br ⟨0⟩]

/-- One clause of a nested problem: leave when `i = pl`; else read the pair `(cpᵢ, len)` at
`pp + 8i`, feed its words, `end_clause()`, `i += 1`. -/
def clauseLoopBody : List Instr :=
  [lget 4, lget 1, igeu, .brIf ⟨1⟩,
    lget 0, lget 4, c32 8, imul, iadd, ld1, lset 14,
    lget 0, lget 4, c32 8, imul, iadd, c32 4, iadd, ld1, lset 15,
    c32 0, lset 13, .block .empty [.loop .empty litLoopBody],
    callf 1,
    lget 4, c32 1, iadd, lset 4, .br ⟨0⟩]

/-- `check-nested(pp, pl, cp, cl)`. -/
def checkNestedBody : List Instr :=
  resetCode ++
  [c32 1, lset 6, c32 0, lset 4, .block .empty [.loop .empty clauseLoopBody]] ++
  certCode

/-! ## The module -/

/-- `[i32 i32 i32 i32] → [i32]`. -/
def ty4 : RecType := ⟨[⟨true, [], .func ⟨[.i32, .i32, .i32, .i32], [.i32]⟩⟩]⟩

/-- The locals of the checks (after the four parameters): twelve `i32`s. -/
def checkLocals : List ValType := List.replicate 12 .i32

/-- **The LRAT acceptor module**: `lratModule`, extended. -/
def prog : Module where
  types := lratModule.types ++ [ty4]
  globals := lratModule.globals ++ [gvar heapBase]
  memories := lratModule.memories ++ [⟨.i32, ⟨16, some 16⟩⟩]
  funcs := lratModule.funcs ++ [
    reallocFunc,
    ⟨⟨3⟩, checkLocals, checkStreamBody⟩,
    ⟨⟨3⟩, checkLocals, checkNestedBody⟩]
  exports := [⟨"memory", .memory ⟨1⟩⟩, ⟨"cabi_realloc", .func ⟨10⟩⟩,
    ⟨"check-stream", .func ⟨11⟩⟩, ⟨"check-nested", .func ⟨12⟩⟩]

/-! ## What the checks read -/

open Silmaril.Logic.SAT.Carrier

/-- The `n` words at byte `p` of the ABI memory (`Silmaril.Wasm.Logic.Words.words`). -/
abbrev wordsAt (B : ByteArray) (p n : Nat) : List (BitVec 32) :=
  Silmaril.Wasm.Logic.Words.words B p n

/-- The nested input of `n` pairs `(ptr, len)` at byte `p`: the words of each pair's block (the
acceptor kit's `list<list<s32>>` reader `Silmaril.Wasm.Acceptor.nestedAt`). -/
abbrev nestedAt (B : ByteArray) (p n : Nat) : Nested := Silmaril.Wasm.Acceptor.nestedAt B p n

/-- Every block of the nested input lies in memory (`Silmaril.Wasm.Acceptor.NestedIn`). -/
abbrev NestedIn (B : ByteArray) (p n : Nat) : Prop := Silmaril.Wasm.Acceptor.NestedIn B p n

/-! ## The instance, and the stores the theorems are about -/

section Inst

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- The instantiated acceptor (`Silmaril.Wasm.Verify.instOf`: validated, instantiated against
no imports). -/
def accI : ScalarInstance := Silmaril.Wasm.Verify.instOf prog

/-- Its store. -/
def accS : Store Nat := accI.store

/-! The elaborator never computes the instance: every fact about it is a kernel check
(`Silmaril.Proofs.Wasm.Examples.LratAccept.Inst`). -/
attribute [irreducible] accI accS

/-- The type of its globals (mutable `i32`). -/
def accGt : CGlobalType := ((accS.globals[0]?).map (·.type)).getD ⟨.const, .botv⟩

/-- The type of the LRAT memory (memory `0`). -/
def lratMemType : MemoryType := ⟨.i32, ⟨1, some 1⟩⟩

/-- The type of the ABI memory (memory `1`). -/
def accMt : MemoryType := ⟨.i32, ⟨16, some 16⟩⟩

/-- **The stores of the acceptor**: the instance's functions, any LRAT state (the eight globals
`G` and the 64 KiB memory `B₀`), the heap pointer `top` (global `8`) and the 1 MiB ABI memory
`B₁` (memory `1`). The instantiated store is one (`G₀`, zero memories, `top = 16`); a call of
an export or a write of the embedder into the ABI memory leads to another. -/
structure AccStore (s : Store Nat) (G : List (BitVec 32)) (B₀ : ByteArray) (top : BitVec 32)
    (B₁ : ByteArray) : Prop where
  funcs : s.funcs = accS.funcs
  globals : s.globals = (G.map fun v => ⟨accGt, Val.i32 v⟩) ++ [⟨accGt, Val.i32 top⟩]
  len : G.length = 8
  mems : s.mems = [⟨lratMemType, B₀⟩, ⟨accMt, B₁⟩]
  size₀ : B₀.size = memSize
  size₁ : B₁.size = memBytes

end Inst

/-! ## The allocator's contract -/

/-- What a call of `cabi_realloc(old, osz, al, nsz)` does when the heap pointer is `top`
(`Silmaril.Wasm.Acceptor.ReallocOk` at `memBytes`): it answers `r` and sets the heap pointer to
`t'`, never lower and within memory; either the block `[r, r + nsz)` is fresh
(`r = align_up(top, al) ≥ top`, `t' = r + nsz`) or the allocation failed (`r = t' = memBytes`). -/
abbrev ReallocOk (top al nsz r t' : BitVec 32) : Prop :=
  Silmaril.Wasm.Acceptor.ReallocOk memBytes top al nsz r t'

end Silmaril.Wasm.Examples.LratAccept
