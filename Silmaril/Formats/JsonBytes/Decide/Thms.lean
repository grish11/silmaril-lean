module

public import Silmaril.Formats.JsonBytes.Decide.Defs
import Silmaril.Proofs.Formats.JsonBytes.Decide

/-!
# The JSON byte language is decidable

* `textB_iff`: `textB p w = true ↔ w ∈ language p`;
* the `Decidable` instances for `w ∈ language p` and `Bytes.IsJson p b`, so closed examples
  are checked by `decide +kernel`;
* `valueB_sound`/`valueB_complete` (and the same for `Elements` and `Members`) relate each rule
  to its fuel-bounded check;
* examples: malformed nested inputs, rejected, and nested inputs, accepted.
-/

@[expose] public section

namespace Silmaril.Formats.JsonBytes

open Decide

theorem Decide.mem_splits {α : Type} {w : List α} {ab : List α × List α} :
    ab ∈ splits w ↔ ab.1 ++ ab.2 = w :=
  Silmaril.Proofs.Formats.JsonBytes.Decide.mem_splits

theorem Decide.valueB_sound {p : Profile} {n : Nat} {w : List UInt8}
    (h : valueB p n w = true) : Value p w :=
  Silmaril.Proofs.Formats.JsonBytes.Decide.valueB_sound h

theorem Decide.valueB_complete {p : Profile} {w : List UInt8} (h : Value p w) {n : Nat}
    (hn : 2 * w.length + 1 ≤ n) : valueB p n w = true :=
  Silmaril.Proofs.Formats.JsonBytes.Decide.valueB_complete h n hn

theorem Decide.elementsB_sound {p : Profile} {n : Nat} {w : List UInt8}
    (h : elementsB p n w = true) : Elements p w :=
  Silmaril.Proofs.Formats.JsonBytes.Decide.elementsB_sound h

theorem Decide.elementsB_complete {p : Profile} {w : List UInt8} (h : Elements p w) {n : Nat}
    (hn : 2 * w.length + 2 ≤ n) : elementsB p n w = true :=
  Silmaril.Proofs.Formats.JsonBytes.Decide.elementsB_complete h n hn

theorem Decide.membersB_sound {p : Profile} {n : Nat} {w : List UInt8}
    (h : membersB p n w = true) : Members p w :=
  Silmaril.Proofs.Formats.JsonBytes.Decide.membersB_sound h

theorem Decide.membersB_complete {p : Profile} {w : List UInt8} (h : Members p w) {n : Nat}
    (hn : 2 * w.length + 2 ≤ n) : membersB p n w = true :=
  Silmaril.Proofs.Formats.JsonBytes.Decide.membersB_complete h n hn

/-- The decision procedure decides the language. -/
theorem Decide.textB_iff {p : Profile} {w : List UInt8} : textB p w = true ↔ w ∈ language p :=
  Silmaril.Proofs.Formats.JsonBytes.Decide.textB_iff

instance language.decidableMem (p : Profile) (w : List UInt8) : Decidable (w ∈ language p) :=
  decidable_of_iff _ Decide.textB_iff

instance _root_.Silmaril.Formats.Bytes.IsJson.decidable (p : Profile) (b : Bytes) :
    Decidable (b.IsJson p) :=
  language.decidableMem p b.toList

/-! ## Examples: nesting, accepted and rejected -/

section Examples

-- `[1,2]`, `[1,]` (trailing comma), `[,1]`, `[1 2]`, `[` and `]`.
example : [0x5B, 0x31, 0x2C, 0x32, 0x5D] ∈ language .rfc8259 := by decide +kernel
example : [0x5B, 0x31, 0x2C, 0x5D] ∉ language .rfc8259 := by decide +kernel
example : [0x5B, 0x2C, 0x31, 0x5D] ∉ language .rfc8259 := by decide +kernel
example : [0x5B, 0x31, 0x20, 0x32, 0x5D] ∉ language .rfc8259 := by decide +kernel
example : [0x5B] ∉ language .rfc8259 := by decide +kernel
example : [0x5D] ∉ language .rfc8259 := by decide +kernel
-- ` [ [ ] , { } ] `, with whitespace everywhere it may occur.
example : [0x20, 0x5B, 0x20, 0x5B, 0x20, 0x5D, 0x20, 0x2C, 0x20, 0x7B, 0x20, 0x7D, 0x20, 0x5D,
    0x20] ∈ language .rfc8259 := by decide +kernel
-- `[[]`, `[]]`, `[}`, `{]`: unbalanced or mismatched brackets.
example : [0x5B, 0x5B, 0x5D] ∉ language .rfc8259 := by decide +kernel
example : [0x5B, 0x5D, 0x5D] ∉ language .rfc8259 := by decide +kernel
example : [0x5B, 0x7D] ∉ language .rfc8259 := by decide +kernel
example : [0x7B, 0x5D] ∉ language .rfc8259 := by decide +kernel
-- `{"a":1}`, `{"a"}`, `{"a":}`, `{1:2}` (names are strings), `{"a":1,}`, `{a:1}`.
example : [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x31, 0x7D] ∈ language .rfc8259 := by decide +kernel
example : [0x7B, 0x22, 0x61, 0x22, 0x7D] ∉ language .rfc8259 := by decide +kernel
example : [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x7D] ∉ language .rfc8259 := by decide +kernel
example : [0x7B, 0x31, 0x3A, 0x32, 0x7D] ∉ language .rfc8259 := by decide +kernel
example : [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x31, 0x2C, 0x7D] ∉ language .rfc8259 := by
  decide +kernel
example : [0x7B, 0x61, 0x3A, 0x31, 0x7D] ∉ language .rfc8259 := by decide +kernel
-- `[1] [2]`: two values.
example : [0x5B, 0x31, 0x5D, 0x20, 0x5B, 0x32, 0x5D] ∉ language .rfc8259 := by decide +kernel
-- `["\uD800"]`: a lone surrogate escape nested in an array, per profile.
example : [0x5B, 0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22, 0x5D] ∈ language .rfc8259 := by
  decide +kernel
example : [0x5B, 0x22, 0x5C, 0x75, 0x44, 0x38, 0x30, 0x30, 0x22, 0x5D] ∉
    language .scalarEscapes := by decide +kernel
-- `{"é":[1E2]}` with a raw UTF-8 name, and the same with an overlong `C0 A9` in the name.
example : [0x7B, 0x22, 0xC3, 0xA9, 0x22, 0x3A, 0x5B, 0x31, 0x45, 0x32, 0x5D, 0x7D] ∈
    language .scalarEscapes := by decide +kernel
example : [0x7B, 0x22, 0xC0, 0xA9, 0x22, 0x3A, 0x5B, 0x31, 0x45, 0x32, 0x5D, 0x7D] ∉
    language .rfc8259 := by decide +kernel
-- `{"a":[1, true],"a":null}` with duplicate names; and with a trailing comma before `}`.
example : [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x5B, 0x31, 0x2C, 0x20, 0x74, 0x72, 0x75, 0x65, 0x5D,
    0x2C, 0x22, 0x61, 0x22, 0x3A, 0x6E, 0x75, 0x6C, 0x6C, 0x7D] ∈ language .scalarEscapes := by
  decide +kernel
example : [0x7B, 0x22, 0x61, 0x22, 0x3A, 0x5B, 0x31, 0x2C, 0x20, 0x74, 0x72, 0x75, 0x65, 0x5D,
    0x2C, 0x22, 0x61, 0x22, 0x3A, 0x6E, 0x75, 0x6C, 0x6C, 0x2C, 0x7D] ∉
    language .scalarEscapes := by decide +kernel
-- A `Bytes` value: `[[]]` with a byte-order mark in front is rejected.
example : ¬ (Bytes.ofList [0xEF, 0xBB, 0xBF, 0x5B, 0x5B, 0x5D, 0x5D]).IsJson .rfc8259 := by
  decide +kernel

end Examples

end Silmaril.Formats.JsonBytes

end
