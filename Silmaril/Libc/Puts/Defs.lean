module

public import Silmaril.Libc.Crypt.Defs

/-! # `puts(3)`: a loose functional spec

`PutsRel` relates the string, the bytes appended to standard output, and the returned `int`.

* **`putsLoose`** (C17 7.21.7.9): success writes `s` and a newline and returns a nonnegative
  value; failure returns `EOF` (`-1`) after writing some prefix of them.
* `putsGlibc`: glibc 2.39 `_IO_puts` returns `MIN (INT_MAX, len + 1)` on success.
* `putsMusl`: musl 1.2.5 `puts` returns `0` on success (`-(r < 0)` with `r ≥ 0`).

These are the functional counterparts of the dynamic-linking study's machine contract
`Silmaril.Elf.Link.Dyn.Libc.putsC` (branch `elf/dynlink-study`), which says only that `puts`
returns to its caller: its machine has no output trace. `LibcSpec.puts` there corresponds to
`Level.putsOnly` in `Silmaril.Libc.Defs`.
-/

@[expose] public section

namespace Silmaril.Libc

/-- A `puts` behaviour: string, bytes written, return value. -/
abbrev PutsRel := CStr → CStr → Int → Prop

/-- `R ⊑ T`. -/
def PutsRel.Le (R T : PutsRel) : Prop := ∀ s w r, R s w r → T s w r

/-- Some outcome for every string. -/
def PutsRel.Progress (R : PutsRel) : Prop := ∀ s, ∃ w r, R s w r

/-- A `puts` of level `T`. -/
def PutsRel.Admissible (T R : PutsRel) : Prop := R.Le T ∧ R.Progress

/-- **The loose `puts`.** -/
def putsLoose : PutsRel := fun s w r =>
  (w = s ++ ['\n'] ∧ 0 ≤ r) ∨ (w <+: s ++ ['\n'] ∧ r = -1)

/-- glibc's success value. -/
def putsGlibc : PutsRel := fun s w r =>
  (w = s ++ ['\n'] ∧ r = min (2 ^ 31 - 1) (s.length + 1 : Int)) ∨ (w <+: s ++ ['\n'] ∧ r = -1)

/-- musl's success value. -/
def putsMusl : PutsRel := fun s w r =>
  (w = s ++ ['\n'] ∧ r = 0) ∨ (w <+: s ++ ['\n'] ∧ r = -1)

end Silmaril.Libc
