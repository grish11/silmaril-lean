module

public import Silmaril.Prelude.Bytes.Defs

/-! # Byte formats and their checkers, on any byte representation

A **byte format** says which byte strings encode which values (an ELF file of its header, a
C string of its characters, a JSON text of a document). It is specified on the **byte list**,
so it means the same thing whatever holds the bytes:

```
structure ByteFormat (α : Type) where
  name   : String                      -- "cstring", "exact", "elf", …
  Parses : List UInt8 → α → Prop       -- the specification: these bytes encode that value
```

A **checker** decides `Parses` for a claimed value on one representation `β` of bytes
(`ByteSource β`: its byte list), and is sound for the format:

```
structure ByteFormat.Checker (F : ByteFormat α) (β : Type) [ByteSource β] where
  check : β → α → Bool
  sound : ∀ b a, check b a = true → F.Parses (ByteSource.bytes b) a
```

The representations provided are `ByteArray` (compiled code, native runs), `KBytes` (the kernel)
and `List UInt8` (the identity: the specification's own representation). A checker never parses;
it checks a value claimed by some parser, possibly an untrusted or external one.

**Pairing native and kernel checks.** A format can have a `ByteArray` checker for compiled code
and a `KBytes` checker for the kernel. Both conclude `F.Parses` of their byte lists, so a check on
either side is a fact about the same bytes as soon as the two sources are equal:
`parses_of_byteArray` takes `t.toByteArray = B` (for instance `x.toByteArray_eq` of
`kbytes_def x of_include raw`, or `kbytes_rel`, which the kernel checks without decoding a byte)
and turns a check of `B` into `F.Parses t.toList a`. No representation is converted inside a
check. `Checker.comap` moves a checker along a map that keeps the bytes (for instance
`KBytes.toByteArray`); that map then runs inside every check, which is cheap in compiled code
and costly in the kernel.

This module has no native evaluation and no trust policy: running a `ByteArray` checker needs
compiled code (`decide` with native evaluation is not allowed here), and registering checkers as
native procedures is the separate trust layer (hiloopai/silmaril-lean#125, whose
`KBytes.FormatChecker α` is a checker on `KBytes` in this sense).

Two reference formats: `exact` (the bytes are the value) and `cstring` (the value and a
terminating NUL, with no NUL inside), each with checkers on all three representations.
-/

@[expose] public section

namespace Silmaril

/-- A representation of byte strings, with the bytes each value holds. -/
class ByteSource (β : Type) where
  /-- The bytes, in order. -/
  bytes : β → List UInt8

/-- The identity: a byte list holds itself. -/
instance : ByteSource (List UInt8) := ⟨id⟩

instance : ByteSource ByteArray := ⟨fun b => b.data.toList⟩

instance : ByteSource KBytes := ⟨KBytes.toList⟩

/-- A data format, specified on byte lists. -/
structure ByteFormat (α : Type) where
  /-- The format's name (`cstring`, `exact`, `elf`, …). -/
  name : String
  /-- The specification: the bytes encode the value. -/
  Parses : List UInt8 → α → Prop

namespace ByteFormat

/-- A sound `Bool` checker of claimed values for `F` on the representation `β`. -/
structure Checker {α : Type} (F : ByteFormat α) (β : Type) [ByteSource β] where
  /-- Decides `F.Parses` for a claimed value. -/
  check : β → α → Bool
  sound : ∀ b a, check b a = true → F.Parses (ByteSource.bytes b) a

/-- A checker along a map that keeps the bytes. The map runs inside every check. -/
def Checker.comap {α β γ : Type} [ByteSource β] [ByteSource γ] {F : ByteFormat α}
    (C : F.Checker β) (f : γ → β) (hf : ∀ g, ByteSource.bytes (f g) = ByteSource.bytes g) :
    F.Checker γ where
  check g a := C.check (f g) a
  sound g a h := hf g ▸ C.sound (f g) a h

/-- A compiled-code checker and a kernel checker of the same format. -/
structure Paired {α : Type} (F : ByteFormat α) where
  native : F.Checker ByteArray
  kernel : F.Checker KBytes

/-! ## Reference formats -/

/-- The bytes are the value. -/
def exact : ByteFormat (List UInt8) := ⟨"exact", fun bs a => bs = a⟩

/-- The bytes are `s` and a terminating NUL, and `s` has no NUL. -/
def cstring : ByteFormat (List UInt8) :=
  ⟨"cstring", fun bs s => bs = s ++ [0] ∧ ∀ c ∈ s, c ≠ 0⟩

/-- `exact` on kernel bytes: lengths, then one wide read compared with one literal. -/
def exactKCheck (t : KBytes) (a : List UInt8) : Bool :=
  t.wf && t.len == a.length && t.read 0 a.length == KBytes.leVal a

/-- `cstring` on kernel bytes, as `exactKCheck` of `s ++ [0]` (#125's `cstringCheck`). -/
def cstringKCheck (t : KBytes) (s : List UInt8) : Bool :=
  s.all (· != 0) && exactKCheck t (s ++ [0])

/-- `exact` on a byte array. -/
def exactBCheck (b : ByteArray) (a : List UInt8) : Bool :=
  b.size == a.length && b.data.toList == a

/-- `cstring` on a byte array. -/
def cstringBCheck (b : ByteArray) (s : List UInt8) : Bool :=
  s.all (· != 0) && exactBCheck b (s ++ [0])

end ByteFormat

end Silmaril
