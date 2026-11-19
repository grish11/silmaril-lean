module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Defs
public import Silmaril.Wasm.Component.Reference.ABI.Memory.Defs
public import Silmaril.Wasm.Component.Reference.ABI.String.Defs

/-!
# Payload decoding against the pure canonical ABI reference loaders: definitions

The vocabulary of `Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Canon`:

* `SPTy`: the **scalar payload types** `bool`, `s32`, `u32`, `s64`, `u64`, with their payload
  type `SPTy.pty` and canonical ABI scalar `SPTy.scalar` (`ABI.Scalar`);
* `SPTy.toScalarValue`, `SPTy.toScalarValues`: a scalar payload value (vector) as the
  `ABI.ScalarValue`s of the reference (`bool` as the bit `1`/`0`, integers as their
  two's-complement bits);
* `loadVals mem ps ptr`: the payload vector of types `ps` at `ptr` in the memory `mem`, decoded
  exactly as `Callout.witNode` does at a call observing `mem` (`ptr` aligned to `valsAlign ps`,
  the `valsWidth ps` bytes in bounds, `readVals` over `segOf mem`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Game.HandleAccept.MemSound

/-- **The scalar payload types**: the `PTy`s that are canonical ABI scalars. -/
inductive SPTy where
  | bool
  | s32
  | u32
  | s64
  | u64
  deriving DecidableEq, Repr

/-- The payload type of a scalar payload type. -/
def SPTy.pty : SPTy → PTy
  | .bool => .bool
  | .s32 => .s32
  | .u32 => .u32
  | .s64 => .s64
  | .u64 => .u64

/-- The canonical ABI scalar of a scalar payload type. -/
def SPTy.scalar : SPTy → ABI.Scalar
  | .bool => .bool
  | .s32 => .s32
  | .u32 => .u32
  | .s64 => .s64
  | .u64 => .u64

/-- **A scalar payload value as a reference scalar value**: a boolean as the bit `1` or `0`,
an integer as its two's-complement bits. -/
def SPTy.toScalarValue : (q : SPTy) → q.pty.Val → ABI.ScalarValue
  | .bool, b => ⟨.bool, if (show Bool from b) then 1 else 0⟩
  | .s32, v => ⟨.s32, (show Int32 from v).toBitVec⟩
  | .u32, v => ⟨.u32, (show UInt32 from v).toBitVec⟩
  | .s64, v => ⟨.s64, (show Int64 from v).toBitVec⟩
  | .u64, v => ⟨.u64, (show UInt64 from v).toBitVec⟩

/-- **A scalar payload vector as a list of reference scalar values.** -/
def SPTy.toScalarValues : (qs : List SPTy) → PTy.Vals (qs.map SPTy.pty) → List ABI.ScalarValue
  | [], _ => []
  | q :: qs, vs =>
      q.toScalarValue (Prod.fst (α := q.pty.Val) vs) ::
        SPTy.toScalarValues qs (Prod.snd (β := PTy.Vals (qs.map SPTy.pty)) vs)

/-- **The payload vector at `ptr`** in the memory `mem`, as `Callout.witNode` decodes it: `ptr`
aligned to `valsAlign ps`, the `valsWidth ps` bytes `[ptr, ptr + valsWidth ps)` in bounds, then
`readVals` with the segments of `mem`. -/
def loadVals (mem : ByteArray) (ps : List PTy) (ptr : Nat) : Option (PTy.Vals ps) :=
  if ptr % valsAlign ps = 0 then
    (segOf mem ptr (valsWidth ps)).bind (readVals (segOf mem) ps)
  else none

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
