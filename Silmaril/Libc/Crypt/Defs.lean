module

/-! # `crypt(3)`: a loose spec and its libc subsets

A **spec level** for `crypt` is a top relation `T : CryptRel`: for a key and a setting, the
results `T k s r` it allows, `r = none` for a null pointer. A real `crypt` is any relation
below `T` that has some result everywhere (`CryptRel.Admissible`; a deterministic `crypt` is
`CryptRel.ofFun f`). So a level is a refinement down-set, as the loose x86 model classes
(`Silmaril.X86.Loose`, `Silmaril.Problems.Core.Admissible`).

C strings are `CStr = List Char`, one `Char` per byte and no `NUL`; lengths are `strlen`.

**What the sources say** (read 2026-11-06):

* POSIX.1-2024 (XSH `crypt`, RETURN VALUE): "Upon successful completion, crypt() shall
  return a pointer to the hashed password; the first two bytes of the returned value shall be
  those of the salt argument. Otherwise, it shall return a null pointer and set errno to
  indicate the error." That is `cryptPosix`.
* glibc 2.39 (`NEWS`, Version 2.39): "libcrypt has been removed from the GNU C Library";
  `libc.so.6` of `libc6 2.39-0ubuntu8.9` exports no `crypt`. The historic glibc libcrypt
  (≤ 2.38) returned a null pointer on failure: `cryptGlibc` is `cryptPosix`.
* libxcrypt 4.4.36 (`libcrypt1 1:4.4.36-4build1`, the `crypt` this Ubuntu system links), its
  `crypt(3)`: on error `crypt` "writes an invalid hash … shorter than 13 characters, will
  begin with a ‘*’, and will not compare equal to setting"; `crypt` "may also return a null
  pointer, or … the invalid hash, depending on how libcrypt was configured"; a success "will
  not contain … ‘*’, ‘!’". Measured here: `crypt("pw", "*") = "*0"`,
  `crypt("pw", "*0") = "*1"`, a 1024-byte key with `$6$abcdefgh` gives `"*0"` (and a
  257-byte key succeeds). That is `cryptXcrypt`: `"*1"` when the setting starts with `*0`, else
  `"*0"`.
* musl 1.2.5 (`src/crypt`, tarball sha256 `a9a118bb…c75e4`): `crypt_r.c` dispatches on
  `$1$` (md5), `$2?$` (bcrypt), `$5$`, `$6$`, everything else DES. The md5, bcrypt, sha256
  and sha512 wrappers return `"*"` on failure; `__crypt_des` returns
  `(setting[0]=='*') ? "x" : "*"`; sha256/sha512 fail for keys over `KEY_MAX = 256` bytes.
  musl's `crypt` never returns a null pointer. That is `cryptMusl`.

**Shapes.** A success is at least 13 bytes (traditional DES is exactly 13; every other method
is longer). A failure token (`FailToken s t`) is shorter than 13 bytes and differs from the
setting `s`; libxcrypt documents both, and musl's tokens meet them (`muslToken_failToken`).

**`cryptLoose`** allows every behaviour of the libcs above: a null pointer, a failure token, or a
success. Each subset is proved below it in `Silmaril.Libc.Crypt.Thms`.
-/

@[expose] public section

namespace Silmaril.Libc

/-- A C string: one `Char` per byte, without the terminating `NUL`. -/
abbrev CStr := List Char

/-- A `crypt` behaviour: key, setting, allowed result (`none` is a null pointer). -/
abbrev CryptRel := CStr → CStr → Option CStr → Prop

/-- `R ⊑ T`: `R` allows only results `T` allows. -/
def CryptRel.Le (R T : CryptRel) : Prop := ∀ k s r, R k s r → T k s r

/-- `R` has some result for every key and setting. -/
def CryptRel.Progress (R : CryptRel) : Prop := ∀ k s, ∃ r, R k s r

/-- `R` is a `crypt` of level `T`: below it, with a result everywhere. -/
def CryptRel.Admissible (T R : CryptRel) : Prop := R.Le T ∧ R.Progress

/-- A deterministic `crypt`. -/
def CryptRel.ofFun (f : CStr → CStr → Option CStr) : CryptRel := fun k s r => r = f k s

/-- A successful result: at least 13 bytes. -/
def IsHash (h : CStr) : Prop := 13 ≤ h.length

/-- A failure token for setting `s`: shorter than 13 bytes and not equal to `s`. -/
def FailToken (s t : CStr) : Prop := t.length < 13 ∧ t ≠ s

/-! ## The levels -/

/-- **`cryptLoose`**: a null pointer, a failure token, or a hash. -/
def cryptLoose : CryptRel := fun _ s r =>
  r = none ∨ (∃ t, r = some t ∧ FailToken s t) ∨ (∃ h, r = some h ∧ IsHash h)

/-- **`cryptPosix`**: a null pointer on failure; on success a hash whose first two bytes are the
setting's. -/
def cryptPosix : CryptRel := fun _ s r =>
  r = none ∨ ∃ h, r = some h ∧ IsHash h ∧ h.take 2 = s.take 2

/-- **`cryptGlibc`**: the historic glibc libcrypt (≤ 2.38), `cryptPosix`. -/
def cryptGlibc : CryptRel := cryptPosix

/-- libxcrypt's token: `"*1"` if the setting starts with `*0`, else `"*0"`. -/
def xcryptToken : CStr → CStr
  | '*' :: '0' :: _ => ['*', '1']
  | _ => ['*', '0']

/-- **`cryptXcrypt`**: libxcrypt with failure tokens (its default, and this system's `crypt`). -/
def cryptXcrypt : CryptRel := fun _ s r => r = some (xcryptToken s) ∨ ∃ h, r = some h ∧ IsHash h

/-- musl's hashing methods (`crypt_r.c`). -/
inductive MuslMethod
  | md5 | bcrypt | sha256 | sha512 | des
  deriving DecidableEq

/-- musl's dispatch (`__crypt_r`): `salt[0]=='$' && salt[1] && salt[2]`, then `$1$`, `$2?$`,
`$5$`, `$6$`; everything else is DES. -/
def muslMethod : CStr → MuslMethod
  | '$' :: '1' :: '$' :: _ => .md5
  | '$' :: '2' :: _ :: '$' :: _ => .bcrypt
  | '$' :: '5' :: '$' :: _ => .sha256
  | '$' :: '6' :: '$' :: _ => .sha512
  | _ => .des

/-- musl's failure token: `"*"`, except DES on a setting starting with `*`, which gives
`"x"`. -/
def muslToken (s : CStr) : CStr :=
  if muslMethod s = .des ∧ s.head? = some '*' then ['x'] else ['*']

/-- musl must fail: sha256 and sha512 reject keys over `KEY_MAX = 256` bytes. -/
def muslMustFail (k s : CStr) : Prop :=
  (muslMethod s = .sha256 ∨ muslMethod s = .sha512) ∧ 256 < k.length

/-- **`cryptMusl`**: the token or a hash, and the token when the key is too long. -/
def cryptMusl : CryptRel := fun k s r =>
  (r = some (muslToken s) ∨ ∃ h, r = some h ∧ IsHash h) ∧
    (muslMustFail k s → r = some (muslToken s))

/-- A deterministic member of `cryptMusl`: always the token (every method fails). -/
def muslAlwaysFails : CStr → CStr → Option CStr := fun _ s => some (muslToken s)

end Silmaril.Libc
