module

public import Silmaril.Prelude.Bytes.Format.Defs
public import Silmaril.Prelude.Bytes.Thms
import Silmaril.Proofs.Prelude.Bytes.Format

/-! # Byte formats: checking on one representation, concluding on the bytes

Proofs are in `Silmaril.Proofs.Prelude.Bytes.Format`.
-/

@[expose] public section

namespace Silmaril.ByteFormat

variable {α : Type} {F : ByteFormat α}

theorem bytes_list (l : List UInt8) : ByteSource.bytes l = l := rfl
theorem bytes_byteArray (b : ByteArray) : ByteSource.bytes b = b.data.toList := rfl
theorem bytes_kbytes (t : KBytes) : ByteSource.bytes t = t.toList := rfl

/-- A successful check is a parse of the checked bytes. -/
theorem Checker.parses_of {β : Type} [ByteSource β] (C : F.Checker β) {b : β} {a : α}
    (h : C.check b a = true) : F.Parses (ByteSource.bytes b) a :=
  C.sound b a h

/-- A check of a byte array is a parse of kernel bytes with the same contents. The equation is
the bridge `kbytes_def … of_include` or `kbytes_rel` proves without evaluation. -/
theorem parses_of_byteArray (C : F.Checker ByteArray) {t : KBytes} {B : ByteArray}
    (hs : t.toByteArray = B) {a : α} (h : C.check B a = true) : F.Parses t.toList a := by
  have := C.sound B a h; rwa [← hs] at this

/-- The two sides of a paired checker conclude the same proposition about the same source. -/
theorem Paired.parses_of_native (P : F.Paired) {t : KBytes} {B : ByteArray}
    (hs : t.toByteArray = B) {a : α} (h : P.native.check B a = true) : F.Parses t.toList a :=
  parses_of_byteArray P.native hs h

theorem Paired.parses_of_kernel (P : F.Paired) {t : KBytes} {a : α}
    (h : P.kernel.check t a = true) : F.Parses t.toList a :=
  P.kernel.sound t a h

/-- Kernel bytes as a byte array keep their bytes (for `Checker.comap`; costly in the kernel). -/
theorem bytes_toByteArray (t : KBytes) : ByteSource.bytes t.toByteArray = ByteSource.bytes t :=
  rfl

/-! ## Reference instances -/

theorem exactKCheck_sound (t : KBytes) (a : List UInt8) (h : exactKCheck t a = true) :
    t.toList = a :=
  Proofs.Prelude.Bytes.exactKCheck_sound t a h

theorem exactBCheck_sound (b : ByteArray) (a : List UInt8) (h : exactBCheck b a = true) :
    b.data.toList = a :=
  Proofs.Prelude.Bytes.exactBCheck_sound b a h

/-- The identity checker of `exact`: `==` on byte lists. -/
def exactList : exact.Checker (List UInt8) where
  check l a := l == a
  sound l a h := by simpa [exact, bytes_list] using h

def exactKBytes : exact.Checker KBytes := ⟨exactKCheck, exactKCheck_sound⟩

def exactByteArray : exact.Checker ByteArray := ⟨exactBCheck, exactBCheck_sound⟩

def exactPaired : exact.Paired := ⟨exactByteArray, exactKBytes⟩

theorem cstring_of_exact {bs s : List UInt8} (hz : s.all (· != 0) = true) (h : bs = s ++ [0]) :
    cstring.Parses bs s :=
  ⟨h, Proofs.Prelude.Bytes.all_ne_zero hz⟩

def cstringList : cstring.Checker (List UInt8) where
  check l s := s.all (· != 0) && l == s ++ [0]
  sound l s h := by
    simp only [Bool.and_eq_true, beq_iff_eq] at h; exact cstring_of_exact h.1 h.2

def cstringKBytes : cstring.Checker KBytes where
  check := cstringKCheck
  sound t s h := by
    simp only [cstringKCheck, Bool.and_eq_true] at h
    exact cstring_of_exact h.1 (exactKCheck_sound t _ h.2)

def cstringByteArray : cstring.Checker ByteArray where
  check := cstringBCheck
  sound b s h := by
    simp only [cstringBCheck, Bool.and_eq_true] at h
    exact cstring_of_exact h.1 (exactBCheck_sound b _ h.2)

def cstringPaired : cstring.Paired := ⟨cstringByteArray, cstringKBytes⟩

end Silmaril.ByteFormat
