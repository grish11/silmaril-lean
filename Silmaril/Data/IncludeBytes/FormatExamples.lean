module

public import Silmaril.Data.IncludeBytes.KBytesExamples
public import Silmaril.Prelude.Bytes.Format.Thms

/-! # Byte formats on `hello-gcc`: kernel and byte-array checks of the same bytes

The interpreter string of the pinned `hello-gcc` is a C string. The kernel checks it on a slice
of the kernel bytes. A `ByteArray` check of the raw `include_bytes` bytes would conclude the same
proposition through the bridge `hello.toByteArray_eq` (stated here with the check as a
hypothesis, since this module runs no native code). On a small literal, the kernel also
evaluates the `ByteArray` checker.
-/

@[expose] public section

namespace Silmaril.IncludeBytes.FormatExamples

open Silmaril Silmaril.ByteFormat Silmaril.KBytes Silmaril.IncludeBytes.KBytesExamples

/-- The interpreter path, checked by the kernel on a slice (one wide read). -/
theorem interp_cstring :
    cstring.Parses (hello.slice 792 28).toList "/lib64/ld-linux-x86-64.so.2".toUTF8.data.toList :=
  cstringKBytes.parses_of (by decide +kernel)

/-- The ELF magic, as the `exact` format on a slice. -/
theorem magic_exact : exact.Parses (hello.slice 0 4).toList [0x7f, 0x45, 0x4c, 0x46] :=
  exactKBytes.parses_of (by decide +kernel)

/-- A byte-array check of the raw file is a fact about the kernel bytes `hello`. -/
example {a : List UInt8} (h : exactByteArray.check helloRaw a = true) :
    exact.Parses hello.toList a :=
  parses_of_byteArray exactByteArray hello.toByteArray_eq h

/-- The `ByteArray` checker on a literal, evaluated by the kernel. -/
example : cstring.Parses (ByteSource.bytes (⟨#[0x68, 0x69, 0]⟩ : ByteArray)) [0x68, 0x69] :=
  cstringByteArray.parses_of (by decide +kernel)

end Silmaril.IncludeBytes.FormatExamples
