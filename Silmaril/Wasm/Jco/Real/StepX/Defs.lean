module

public import Silmaril.Wasm.Jco.Real.Step.Defs

/-!
# Adaptor code with `memory.copy`, `if` and stores against the reference engine: definitions

`Silmaril.Wasm.Jco.Real.Step` relates the adaptor instructions of the fragment `Frag` to Core 3.0.
Three instruction families are outside `Frag`, and each needs a fact that the abstract semantics
`XInstr.step` does not check:

* **`if … else … end`**: an `XInstr` branch runs on the whole operand stack, a Wasm block only
  on its own values; the two agree when the branch neither pops below its own values nor leaves
  more or fewer values than its block type says;
* **stores**: the abstract store writes the low bytes of any value, Core's `i32.store8` etc.
  needs a value of the store's type;
* **`memory.copy`**: Core copies byte by byte, advancing `i32` addresses modulo `2^32`; the
  abstract `memmove` uses unbounded addresses. They agree on a memory of at most `2^32` bytes.

The first two are what Wasm **validation** guarantees, so this module states them by a small
type checker, the third by an invariant of the store:

* `tyStep rt lt i ts`, `tyExec rt lt is ts`: the operand-stack types (top first) after `i` (`is`),
  from the stack types `ts`, with local types `lt` and result types `rt g` of the wrapped export
  `g`; `none` when the code is ill-typed **or outside the fragment**. The fragment is `Frag`'s
  instructions, `memory.copy`, `if` with a value or empty block type whose branches have that
  type from an empty stack, and the integer stores of a width Wasm has at an offset below
  `2^32`; float loads and stores are not in it;
* `Typed lt ts f`: the frame `f` has local types `lt` and stack types `ts`;
* `CallsTyped M rt`: every returned call of export `g` of `M` returns values of types `rt g`
  (what Core's type soundness gives for an export of result type `rt g`; a hypothesis here);
* `MemOk ma s`: the memory instance at `ma` exists and has at most `2^32` bytes;
  `CallsKeepMem P host mi ma`: calls of the wrapped instance preserve `MemOk` (a hypothesis: for a
  32-bit memory whose size is its page count times `2^16` it follows from `memory.grow`'s limit);
* `CallsTrapCore P host mi ma`: a trap of a call of the wrapped instance is a Core trap (used
  only for the trap theorems).

The theorems are in `Silmaril.Wasm.Jco.Real.StepX.Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Real

open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm (IntType NumType)

/-- The `i32` number type. -/
abbrev tI32 : NumType := .int .i32

mutual
/-- **The stack types after one instruction** (top first), or `none` if it is ill-typed or
outside the fragment. -/
def tyStep (rt : String → List NumType) (lt : List NumType) :
    XInstr → List NumType → Option (List NumType)
  | .base (.localGet i), ts => if i < 2 ^ 32 then lt[i]?.map (· :: ts) else none
  | .base (.localSet i), t :: ts => if i < 2 ^ 32 ∧ lt[i]? = some t then some ts else none
  | .base (.i32Const _), ts => some (tI32 :: ts)
  | .base (.call g n), ts => if n ≤ ts.length then some ((rt g).reverse ++ ts.drop n) else none
  | .i32Eqz, t :: ts => if t = tI32 then some (tI32 :: ts) else none
  | .i32LtU, t₁ :: t₂ :: ts => if t₁ = tI32 ∧ t₂ = tI32 then some (tI32 :: ts) else none
  | .select, c :: b :: a :: ts => if c = tI32 ∧ a = b then some (a :: ts) else none
  | .memCopy, t₁ :: t₂ :: t₃ :: ts =>
    if t₁ = tI32 ∧ t₂ = tI32 ∧ t₃ = tI32 then some ts else none
  | .ifElse res thn els, c :: ts =>
    if c = tI32 ∧ tyExec rt lt thn [] = some res.toList ∧ tyExec rt lt els [] = some res.toList
    then some (res.toList ++ ts) else none
  | .load (.int it) n _ off, a :: ts =>
    if a = tI32 ∧ intWidthOk it n = true ∧ off < 2 ^ 32 then some (.int it :: ts) else none
  | .store (.int it) n off, t :: a :: ts =>
    if t = .int it ∧ a = tI32 ∧ intWidthOk it n = true ∧ off < 2 ^ 32 then some ts else none
  | _, _ => none

/-- **The stack types after a sequence**, or `none`. -/
def tyExec (rt : String → List NumType) (lt : List NumType) :
    List XInstr → List NumType → Option (List NumType)
  | [], ts => some ts
  | i :: is, ts =>
    match tyStep rt lt i ts with
    | some ts' => tyExec rt lt is ts'
    | none => none
end

/-- The frame `f` has local types `lt` and operand-stack types `ts` (top first). -/
def Typed (lt ts : List NumType) (f : Silmaril.Wasm.Jco.Frame) : Prop :=
  f.locals.map (·.type) = lt ∧ f.stack.map (·.type) = ts

/-- Every returned call of the export `g` returns values of the types `rt g`. -/
def CallsTyped (M : CoreInst) (rt : String → List NumType) : Prop :=
  ∀ (g : String) (args rs : List Flat) (s s' : M.St), M.call g args s (.ok rs s') →
    rs.map (·.type) = rt g

/-- The memory instance at store address `ma` exists and has at most `2^32` bytes. -/
def MemOk {H : Type} (ma : Nat) (s : Store H) : Prop :=
  ∃ m, s.mems[ma]? = some m ∧ m.bytes.size ≤ 2 ^ 32

/-- Returned calls of the wrapped instance preserve `MemOk`. -/
def CallsKeepMem {H : Type} (P : Profile) (host : HostSemantics H)
    (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) : Prop :=
  ∀ (g : String) (args rs : List Flat) (s s' : Store H),
    (realInst H P host mi ma).call g args s (.ok rs s') → MemOk ma s → MemOk ma s'

/-- A trap of a call of the wrapped instance is a Core 3.0 trap: the export exists, the invocation
is well formed, and its `$invoke` run reaches `trap` (not an uncaught exception, an ill-typed
invocation or a non-flat result, which `realInst` also reads as traps). -/
def CallsTrapCore {H : Type} (P : Profile) (host : HostSemantics H)
    (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) : Prop :=
  ∀ (g : String) (args : List Flat) (s : Store H),
    (realInst H P host mi ma).call g args s .trap →
    ∃ a c, Silmaril.Wasm.Binaryen.exportFunc? mi g = some a ∧ InvokeOk s a (args.map toVal) ∧
      Steps P host (invoke s a (args.map toVal)) c ∧ c.code = [.trap]

end Silmaril.Wasm.Jco.Real
