module

public import Silmaril.Wasm.Acceptor.Abi.Defs
import Silmaril.Proofs.Wasm.Acceptor.Abi

/-!
# The acceptor kit: reading canonical-ABI arguments back from memory, results

Proofs in `Silmaril.Proofs.Wasm.Acceptor.Abi`.

* **The reader contracts** (`Reads`): `reads_s32`, `reads_u32` (`wd`), `reads_s64` (`wd64`);
  `Reads.list` (a list's `(ptr, len)` pair, `pairAt`, its block in bounds, `listIn`);
  `Reads.tuple2`, `Reads.record2` (two fields at `fieldOff₁`, `fieldOff₂`, `read2`);
  `Reads.map` (through a bijection `f ∘ g = id`), `Reads.mono` (weaker bounds);
  `reads_words` (a `list<s32>` inside a list).
* **`holdsL_listAt`**: a lowered top-level `list<t>` reads back with `listAt t.size rd`, each
  element meeting the bounds.
* **`flatHolds_two`**, **`flatHolds_read2`**: two lowered list arguments (`FlatHolds`, as
  `params_holds` ends): the flat arguments `(q₁, len₁, q₂, len₂)`, the blocks in bounds
  (`ListIn`) and the values read back (`listAt`).
* **`checkList_map`**: the values of an encoded list have the element type (for
  `CheckerExport.typed`).
* **`nestedAt_eq`**, **`nestedIn_iff`**, **`words_eq`**: the `list<list<s32>>` and `list<s32>`
  readers are instances.
-/

@[expose] public section

namespace Silmaril.Wasm.Acceptor

open Silmaril.Wasm.Component.Reference.ListLift (LTy LVal Holds HoldsL FlatHolds wd64)
open Silmaril.Wasm.Logic.Words (wd words)

variable {α β : Type} {B : ByteArray} {lo hi : Nat}

theorem listAt_succ (sz : Nat) (rd : ByteArray → Nat → α) (B : ByteArray) (p n : Nat) :
    listAt sz rd B p (n + 1) = rd B p :: listAt sz rd B (p + sz) n :=
  Silmaril.Proofs.Wasm.Acceptor.listAt_succ sz rd B p n

@[simp] theorem length_listAt (sz : Nat) (rd : ByteArray → Nat → α) (B : ByteArray) (p n : Nat) :
    (listAt sz rd B p n).length = n :=
  Silmaril.Proofs.Wasm.Acceptor.length_listAt sz rd B p n

theorem reads_s32 : Reads .s32 LVal.s32 wd NoBounds := Silmaril.Proofs.Wasm.Acceptor.reads_s32

theorem reads_u32 : Reads .u32 LVal.u32 wd NoBounds := Silmaril.Proofs.Wasm.Acceptor.reads_u32

theorem reads_s64 : Reads .s64 LVal.s64 wd64 NoBounds := Silmaril.Proofs.Wasm.Acceptor.reads_s64

/-- **A list**: the `(ptr, len)` pair at `p`, its block in bounds. -/
theorem Reads.list {t : LTy} {enc : α → LVal} {rd : ByteArray → Nat → α}
    {inn : ByteArray → Nat → Prop} (h : Reads t enc rd inn) :
    Reads (.list t) (fun xs => .list (xs.map enc)) (pairAt t.size rd) (listIn t inn) :=
  Silmaril.Proofs.Wasm.Acceptor.Reads.list h

/-- **A two-field tuple**, the fields at their canonical-ABI offsets. -/
theorem Reads.tuple2 {t₁ t₂ : LTy} {e₁ : α → LVal} {e₂ : β → LVal} {r₁ : ByteArray → Nat → α}
    {r₂ : ByteArray → Nat → β} {i₁ i₂ : ByteArray → Nat → Prop} (h₁ : Reads t₁ e₁ r₁ i₁)
    (h₂ : Reads t₂ e₂ r₂ i₂) :
    Reads (.tuple t₁ [t₂]) (enc2 e₁ e₂) (read2 t₁ t₂ r₁ r₂) (in2 t₁ t₂ i₁ i₂) :=
  Silmaril.Proofs.Wasm.Acceptor.Reads.tuple2 h₁ h₂

/-- **A two-field record**, the fields at their canonical-ABI offsets. -/
theorem Reads.record2 {t₁ t₂ : LTy} {e₁ : α → LVal} {e₂ : β → LVal} {r₁ : ByteArray → Nat → α}
    {r₂ : ByteArray → Nat → β} {i₁ i₂ : ByteArray → Nat → Prop} (name l l₂ : String)
    (h₁ : Reads t₁ e₁ r₁ i₁) (h₂ : Reads t₂ e₂ r₂ i₂) :
    Reads (.record name l t₁ [(l₂, t₂)]) (enc2 e₁ e₂) (read2 t₁ t₂ r₁ r₂) (in2 t₁ t₂ i₁ i₂) :=
  Silmaril.Proofs.Wasm.Acceptor.Reads.record2 name l l₂ h₁ h₂

/-- **A type in bijection with a read one.** -/
theorem Reads.map {t : LTy} {enc : α → LVal} {rd : ByteArray → Nat → α}
    {inn : ByteArray → Nat → Prop} (h : Reads t enc rd inn) (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) : Reads t (fun b => enc (g b)) (fun B p => f (rd B p)) inn :=
  Silmaril.Proofs.Wasm.Acceptor.Reads.map h f g hfg

/-- **Weaker bounds.** -/
theorem Reads.mono {t : LTy} {enc : α → LVal} {rd : ByteArray → Nat → α}
    {inn inn' : ByteArray → Nat → Prop} (h : Reads t enc rd inn)
    (hi : ∀ B p, inn B p → inn' B p) : Reads t enc rd inn' :=
  Silmaril.Proofs.Wasm.Acceptor.Reads.mono h hi

/-- `list<s32>` elements of a `list<list<s32>>`. -/
theorem reads_words : Reads (.list .s32) LVal.ofWords (pairAt 4 wd) (PairIn 4) :=
  Silmaril.Proofs.Wasm.Acceptor.reads_words

/-- Typing of encoded lists: each element's value has the element type. -/
theorem checkList_map {t : LTy} {f : α → LVal} (h : ∀ a, t.check (f a) = true) (l : List α) :
    LTy.checkList t (l.map f) = true :=
  Silmaril.Proofs.Wasm.Acceptor.checkList_map h l

/-- **A lowered top-level `list<t>`**, read back. -/
theorem holdsL_listAt {t : LTy} {enc : α → LVal} {rd : ByteArray → Nat → α}
    {inn : ByteArray → Nat → Prop} (h : Reads t enc rd inn) (xs : List α) (q : Nat)
    (hL : HoldsL B lo hi t (xs.map enc) q) :
    listAt t.size rd B q xs.length = xs ∧ ∀ i < xs.length, inn B (q + t.size * i) :=
  Silmaril.Proofs.Wasm.Acceptor.holdsL_listAt h xs q hL

/-- **Two lowered list arguments.** -/
theorem flatHolds_two {t₁ t₂ : LTy} {us vs : List LVal}
    {fl : List Silmaril.Wasm.Execution.Core.Val}
    (h : FlatHolds B lo hi [.list t₁, .list t₂] [.list us, .list vs] fl) :
    ∃ q₁ q₂, fl = [.i32 (BitVec.ofNat 32 q₁), .i32 (BitVec.ofNat 32 us.length),
        .i32 (BitVec.ofNat 32 q₂), .i32 (BitVec.ofNat 32 vs.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ us.length < 2 ^ 32 ∧ vs.length < 2 ^ 32 ∧
      q₁ + us.length * t₁.size ≤ B.size ∧ HoldsL B lo hi t₁ us q₁ ∧
      q₂ + vs.length * t₂.size ≤ B.size ∧ HoldsL B lo hi t₂ vs q₂ :=
  Silmaril.Proofs.Wasm.Acceptor.flatHolds_two h

/-- **Two lowered list arguments, read back.** -/
theorem flatHolds_read2 {t₁ t₂ : LTy} {e₁ : α → LVal} {e₂ : β → LVal} {r₁ : ByteArray → Nat → α}
    {r₂ : ByteArray → Nat → β} {i₁ i₂ : ByteArray → Nat → Prop} (h₁ : Reads t₁ e₁ r₁ i₁)
    (h₂ : Reads t₂ e₂ r₂ i₂) {xs : List α} {ys : List β}
    {fl : List Silmaril.Wasm.Execution.Core.Val}
    (h : FlatHolds B lo hi [.list t₁, .list t₂] [.list (xs.map e₁), .list (ys.map e₂)] fl) :
    ∃ q₁ q₂, fl = [.i32 (BitVec.ofNat 32 q₁), .i32 (BitVec.ofNat 32 xs.length),
        .i32 (BitVec.ofNat 32 q₂), .i32 (BitVec.ofNat 32 ys.length)] ∧
      q₁ < 2 ^ 32 ∧ q₂ < 2 ^ 32 ∧ xs.length < 2 ^ 32 ∧ ys.length < 2 ^ 32 ∧
      ListIn t₁.size i₁ B q₁ xs.length ∧ listAt t₁.size r₁ B q₁ xs.length = xs ∧
      ListIn t₂.size i₂ B q₂ ys.length ∧ listAt t₂.size r₂ B q₂ ys.length = ys :=
  Silmaril.Proofs.Wasm.Acceptor.flatHolds_read2 h₁ h₂ h

/-! ## Instances -/

theorem words_eq (B : ByteArray) (p n : Nat) : words B p n = listAt 4 wd B p n := rfl

theorem nestedAt_eq (B : ByteArray) (p n : Nat) : nestedAt B p n = listAt 8 (pairAt 4 wd) B p n :=
  rfl

theorem nestedIn_iff (B : ByteArray) (p n : Nat) : NestedIn B p n ↔ ListIn 8 (PairIn 4) B p n :=
  Iff.rfl

end Silmaril.Wasm.Acceptor
