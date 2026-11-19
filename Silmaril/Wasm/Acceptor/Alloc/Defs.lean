module

public import Silmaril.Wasm.Examples.LRAT.Defs
public import Silmaril.Wasm.Component.Reference.ListLift.Bump.Defs

/-!
# The acceptor kit: the bump allocator `cabi_realloc`

One `cabi_realloc` for every acceptor module, as a Lean Wasm AST builder: `reallocFunc ty g N`
is the function of type `ty` whose heap pointer is global `g` of its module, for an ABI memory
of `N` bytes. The SAT, LRAT and Farkas acceptors (`Silmaril.Wasm.Examples.{SatAccept,
LratAccept,FarkasAccept}`) all use it, at their own global index and memory size.

**What it computes** (`cabi_realloc(old, old_size, align, new_size) -> ptr`, locals `4` `p` and
`5` "fits"): it ignores the old block (the canonical ABI only allocates fresh lists), computes
`p = align_up(top, align) = (top + (align - 1)) & -align` in `i32`, and

* when `top ≤ p`, `p ≤ N` and `new_size ≤ N - p` (unsigned), sets `top := p + new_size` and
  answers `p`;
* otherwise sets `top := N` and answers `N`, so a nonempty list then fails the canonical ABI's
  bounds check (a trap) and an empty one sits at the end of memory.

It never traps and never lowers `top`, so the blocks it answers within memory are disjoint and
lie above every earlier block. The memory index plays no part in the code: the allocator only
reads and writes its global. Which memory the blocks are in is the component's choice
(`ListComp.memIdx`), and enters only `BumpSpec.bumpAlloc` (`Thms`).

* `ReallocOk N top al nsz r t'`: what a returning run does, from heap pointer `top`;
* `BumpSpec P ra ga N Inv`: the allocator at function address `ra` bumps the global at address
  `ga` within `N` bytes, from the stores of the invariant `Inv` (heap pointer `t`), and setting
  that global within `N` keeps `Inv`. From it, with the size and write facts of the ABI memory,
  `BumpSpec.bumpAlloc` derives `ListLift.BumpAlloc`, which `params_holds` consumes.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm
open Silmaril.Wasm.Examples.LRAT (c32 lget lset gget gset iadd isub iand igeu ieqz
  ifThen)
open Silmaril.Wasm.Execution.Core (Store Steps invoke vals Val)
open Silmaril.Wasm.Numerics (Profile)

/-- **The body of `cabi_realloc(old, osz, al, nsz)`** with heap pointer global `g` and memory
size `N`. Locals: `4` `p`; `5` "fits". -/
def reallocBody (g N : Nat) : List Instr :=
  -- p := (top + al - 1) & -al
  [gget g, lget 2, c32 1, isub, iadd, c32 0, lget 2, isub, iand, lset 4,
    -- fits := top ≤ p ∧ p ≤ N ∧ nsz ≤ N - p
    lget 4, gget g, igeu, c32 N, lget 4, igeu, iand,
      c32 N, lget 4, isub, lget 3, igeu, iand, lset 5,
    lget 5, ifThen [lget 4, lget 3, iadd, gset g],
    lget 5, ieqz, ifThen [c32 N, gset g, c32 N, lset 4],
    lget 4]

/-- The locals of `cabi_realloc` after its four parameters. -/
def reallocLocals : List ValType := [.i32, .i32]

/-- **`cabi_realloc`** as a module function of type `ty` (`[i32 i32 i32 i32] → [i32]`). -/
def reallocFunc (ty : TypeIdx) (g N : Nat) : Func := ⟨ty, reallocLocals, reallocBody g N⟩

/-- `align_up(top, al)` as `cabi_realloc` computes it, in `i32` (for every `al`, including `0`
and non-powers of two). -/
def alignUp (top al : BitVec 32) : BitVec 32 :=
  (top + (al - BitVec.ofNat 32 1)) &&& (BitVec.ofNat 32 0 - al)

/-- What a call of `cabi_realloc(old, osz, al, nsz)` does when the heap pointer is `top`: it
answers `r` and sets the heap pointer to `t'`, never lower and within `N`; either the block
`[r, r + nsz)` is fresh (`r = align_up(top, al) ≥ top`, `t' = r + nsz`) or the allocation failed
(`r = t' = N`). -/
def ReallocOk (N : Nat) (top al nsz r t' : BitVec 32) : Prop :=
  top.toNat ≤ t'.toNat ∧ t'.toNat ≤ N ∧
    ((r = alignUp top al ∧ top.toNat ≤ r.toNat ∧ r.toNat + nsz.toNat = t'.toNat) ∨
      (r.toNat = N ∧ t'.toNat = N))

/-- **A bump allocator on a global**: the function at address `ra` is an allocator whose heap
pointer is the `i32` global at address `ga`, in the stores of `Inv` (`Inv s t`: heap pointer
`t ≤ N`). Every returning run from such a store answers one value and only sets that global, as
`ReallocOk N` says, and setting the global to a value within `N` keeps the invariant. -/
structure BumpSpec (P : Profile) (ra ga N : Nat) (Inv : Store Nat → Nat → Prop) : Prop where
  /-- The memory is 32-bit addressable. -/
  small : N < 2 ^ 32
  /-- The heap pointer is within memory. -/
  le : ∀ {s t}, Inv s t → t ≤ N
  /-- Every returning run of the allocator. -/
  run : ∀ {s t} {old osz al nsz : BitVec 32} {s' f' res}, Inv s t →
    Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (invoke s ra [.i32 old, .i32 osz, .i32 al, .i32 nsz]) ⟨s', f', vals res⟩ →
    ∃ r t' : BitVec 32, res = [.i32 r] ∧ s' = s.setGlobal ga (.i32 t') ∧
      ReallocOk N (BitVec.ofNat 32 t) al nsz r t'
  /-- Setting the heap pointer within memory keeps the invariant. -/
  set : ∀ {s t} {t' : BitVec 32}, Inv s t → (BitVec.ofNat 32 t).toNat ≤ t'.toNat →
    t'.toNat ≤ N → Inv (s.setGlobal ga (.i32 t')) t'.toNat

end Silmaril.Wasm.Acceptor
