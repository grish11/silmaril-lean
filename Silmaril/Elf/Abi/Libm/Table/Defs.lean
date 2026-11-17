module

public import Silmaril.Elf.Ast.Defs
public import Silmaril.Elf.Lookup.Defs

/-! # glibc 2.36 `libm.so.6`: the classification of the claimable `math.h` functions (generated: do not edit)

Written by `scripts/libm-rows/gen.py` from `examples/elf/pinned/glibc-2.36-libm.so.6` (SHA-256 `7f2ca87f652f56b094462474b076749e90e689d0ecb9cb63c7679820b271b4e7`) and
`scripts/libm-rows/claimable.lean`; `gen.py --check` regenerates it and compares byte for byte.
Untrusted data: `Silmaril.Elf.Abi.Libm.Thms` checks every entry against the import (`classes_names`) and the
file's parse (`classes_check`), and the row bytes against the file (`*_code`). -/

@[expose] public section

namespace Silmaril.Elf.Abi.Libm

open Silmaril.Elf

/-- **What ld.so's lookup of a function's default version finds** in the file: a plain
`STT_FUNC` definition (version, `.dynsym` index, `st_value`, `st_size`), an `STT_GNU_IFUNC`
definition (version, index: the resolver chooses the code at load time), or no definition. -/
inductive Class where
  | plain (ver : Ver) (index value size : Nat)
  | ifunc (ver : Ver) (index : Nat)
  | absent
  deriving DecidableEq, Repr

/-- The version `GLIBC_2.18` as a reference requests it: name, ELF hash, not hidden. -/
def v2_18 : Ver := ⟨nameOf "GLIBC_2.18", 110530968, false⟩

/-- The version `GLIBC_2.2.5` as a reference requests it: name, ELF hash, not hidden. -/
def v2_2_5 : Ver := ⟨nameOf "GLIBC_2.2.5", 157882997, false⟩

/-- The version `GLIBC_2.23` as a reference requests it: name, ELF hash, not hidden. -/
def v2_23 : Ver := ⟨nameOf "GLIBC_2.23", 110530947, false⟩

/-- The version `GLIBC_2.25` as a reference requests it: name, ELF hash, not hidden. -/
def v2_25 : Ver := ⟨nameOf "GLIBC_2.25", 110530949, false⟩

/-- The version `GLIBC_2.27` as a reference requests it: name, ELF hash, not hidden. -/
def v2_27 : Ver := ⟨nameOf "GLIBC_2.27", 110530951, false⟩

/-- The version `GLIBC_2.29` as a reference requests it: name, ELF hash, not hidden. -/
def v2_29 : Ver := ⟨nameOf "GLIBC_2.29", 110530953, false⟩

/-- The version `GLIBC_2.35` as a reference requests it: name, ELF hash, not hidden. -/
def v2_35 : Ver := ⟨nameOf "GLIBC_2.35", 110530997, false⟩

/-- **Every claimable function of the pinned `math.h`, in the import's order**, with what ld.so's lookup
of its default version finds in the file (`Class`). -/
def classes : List (String × Class) := [
  ("__fpclassify", .plain v2_2_5 810 0x30bf0 69),
  ("__signbit", .plain v2_2_5 208 0x32c70 10),
  ("__isinf", .absent),
  ("__finite", .plain v2_2_5 382 0x32980 26),
  ("__isnan", .absent),
  ("__iseqsig", .plain v2_25 921 0x38ec0 55),
  ("__issignaling", .plain v2_18 1211 0x32900 35),
  ("acos", .plain v2_2_5 248 0x127c0 88),
  ("__acos", .absent),
  ("asin", .plain v2_2_5 646 0x12860 88),
  ("__asin", .absent),
  ("atan", .ifunc v2_2_5 442),
  ("__atan", .absent),
  ("atan2", .plain v2_2_5 654 0x128c0 198),
  ("__atan2", .absent),
  ("cos", .ifunc v2_2_5 639),
  ("__cos", .absent),
  ("sin", .ifunc v2_2_5 1035),
  ("__sin", .absent),
  ("tan", .ifunc v2_2_5 813),
  ("__tan", .absent),
  ("cosh", .plain v2_2_5 945 0x129e0 96),
  ("__cosh", .absent),
  ("sinh", .plain v2_2_5 613 0x13420 96),
  ("__sinh", .absent),
  ("tanh", .plain v2_2_5 1087 0x30ab0 315),
  ("__tanh", .absent),
  ("acosh", .plain v2_2_5 584 0x12820 50),
  ("__acosh", .absent),
  ("asinh", .plain v2_2_5 245 0x2cb40 410),
  ("__asinh", .absent),
  ("atanh", .plain v2_2_5 712 0x12990 70),
  ("__atanh", .absent),
  ("exp", .plain v2_29 35 0x39370 95),
  ("__exp", .absent),
  ("frexp", .plain v2_2_5 496 0x32bd0 146),
  ("__frexp", .absent),
  ("ldexp", .plain v2_2_5 876 0x32c80 126),
  ("__ldexp", .absent),
  ("log", .plain v2_29 456 0x39270 57),
  ("__log", .absent),
  ("log10", .plain v2_2_5 227 0x12fc0 114),
  ("__log10", .absent),
  ("modf", .plain v2_2_5 1001 0x329c0 239),
  ("__modf", .absent),
  ("expm1", .ifunc v2_2_5 1057),
  ("__expm1", .absent),
  ("log1p", .plain v2_2_5 321 0x39010 57),
  ("__log1p", .absent),
  ("logb", .plain v2_2_5 913 0x2e760 125),
  ("__logb", .absent),
  ("exp2", .plain v2_29 962 0x393d0 570),
  ("__exp2", .absent),
  ("log2", .ifunc v2_29 862),
  ("__log2", .absent),
  ("pow", .plain v2_29 931 0x392b0 181),
  ("__pow", .absent),
  ("sqrt", .plain v2_2_5 513 0x13480 42),
  ("__sqrt", .absent),
  ("hypot", .plain v2_35 484 0x27ae0 932),
  ("__hypot", .absent),
  ("cbrt", .plain v2_2_5 631 0x2d210 367),
  ("__cbrt", .absent),
  ("ceil", .ifunc v2_2_5 602),
  ("__ceil", .absent),
  ("fabs", .plain v2_2_5 433 0x2e380 9),
  ("__fabs", .absent),
  ("floor", .ifunc v2_2_5 168),
  ("__floor", .absent),
  ("fmod", .plain v2_2_5 1116 0x12b40 76),
  ("__fmod", .absent),
  ("isinf", .absent),
  ("finite", .plain v2_2_5 199 0x32980 26),
  ("drem", .plain v2_2_5 915 0x13230 90),
  ("__drem", .absent),
  ("significand", .plain v2_2_5 476 0x38f40 40),
  ("__significand", .absent),
  ("copysign", .plain v2_2_5 332 0x329a0 29),
  ("__copysign", .absent),
  ("nan", .plain v2_2_5 134 0x38eb0 9),
  ("__nan", .absent),
  ("isnan", .absent),
  ("j0", .plain v2_2_5 1030 0x12c10 65),
  ("__j0", .absent),
  ("j1", .plain v2_2_5 1031 0x12d20 65),
  ("__j1", .absent),
  ("jn", .plain v2_2_5 1104 0x12e30 77),
  ("__jn", .absent),
  ("y0", .plain v2_2_5 428 0x12c60 186),
  ("__y0", .absent),
  ("y1", .plain v2_2_5 430 0x12d70 186),
  ("__y1", .absent),
  ("yn", .plain v2_2_5 503 0x12e80 188),
  ("__yn", .absent),
  ("erf", .plain v2_2_5 972 0x2d3b0 1438),
  ("__erf", .absent),
  ("erfc", .plain v2_2_5 1142 0x2d950 1481),
  ("__erfc", .absent),
  ("lgamma", .plain v2_23 297 0x137c0 239),
  ("__lgamma", .absent),
  ("tgamma", .plain v2_2_5 265 0x134b0 536),
  ("__tgamma", .absent),
  ("gamma", .plain v2_2_5 319 0x13930 394),
  ("__gamma", .absent),
  ("lgamma_r", .plain v2_2_5 423 0x136d0 231),
  ("__lgamma_r", .absent),
  ("rint", .ifunc v2_2_5 447),
  ("__rint", .absent),
  ("nextafter", .plain v2_2_5 1017 0x2e7e0 426),
  ("__nextafter", .absent),
  ("remainder", .plain v2_2_5 25 0x13230 90),
  ("__remainder", .absent),
  ("scalbn", .plain v2_2_5 1012 0x32c80 126),
  ("__scalbn", .absent),
  ("ilogb", .plain v2_2_5 125 0x38f70 60),
  ("__ilogb", .absent),
  ("scalbln", .plain v2_2_5 546 0x39050 126),
  ("__scalbln", .absent),
  ("nearbyint", .ifunc v2_2_5 893),
  ("__nearbyint", .absent),
  ("round", .plain v2_2_5 107 0x311c0 142),
  ("__round", .absent),
  ("trunc", .ifunc v2_2_5 844),
  ("__trunc", .absent),
  ("remquo", .plain v2_2_5 393 0x30c70 535),
  ("__remquo", .absent),
  ("lrint", .plain v2_2_5 1135 0x32760 6),
  ("__lrint", .absent),
  ("llrint", .plain v2_2_5 1119 0x32760 6),
  ("__llrint", .absent),
  ("lround", .plain v2_2_5 89 0x32770 147),
  ("__lround", .absent),
  ("llround", .plain v2_2_5 224 0x32770 147),
  ("__llround", .absent),
  ("fdim", .plain v2_2_5 1048 0x38da0 87),
  ("__fdim", .absent),
  ("fmax", .plain v2_2_5 578 0x38e30 61),
  ("__fmax", .absent),
  ("fmin", .plain v2_2_5 877 0x38e70 61),
  ("__fmin", .absent),
  ("fma", .ifunc v2_2_5 878),
  ("__fma", .absent),
  ("scalb", .plain v2_2_5 413 0x13350 198),
  ("__scalb", .absent),
  ("__fpclassifyf", .plain v2_2_5 1128 0x40ff0 58),
  ("__signbitf", .plain v2_2_5 374 0x41ab0 8),
  ("__isinff", .absent),
  ("__finitef", .plain v2_2_5 1195 0x41880 18),
  ("__isnanf", .absent),
  ("__iseqsigf", .plain v2_25 1174 0x47620 55),
  ("__issignalingf", .plain v2_18 145 0x41810 26),
  ("acosf", .plain v2_2_5 583 0x16120 87),
  ("__acosf", .absent),
  ("asinf", .plain v2_2_5 240 0x161c0 87),
  ("__asinf", .absent),
  ("atanf", .plain v2_2_5 706 0x3f430 622),
  ("__atanf", .absent),
  ("atan2f", .plain v2_2_5 260 0x16220 196),
  ("__atan2f", .absent),
  ("cosf", .ifunc v2_2_5 943),
  ("__cosf", .absent),
  ("sinf", .ifunc v2_2_5 609),
  ("__sinf", .absent),
  ("tanf", .plain v2_2_5 1086 0x40d70 367),
  ("__tanf", .absent),
  ("coshf", .plain v2_2_5 605 0x16340 91),
  ("__coshf", .absent),
  ("sinhf", .plain v2_2_5 454 0x16d40 91),
  ("__sinhf", .absent),
  ("tanhf", .plain v2_2_5 270 0x40ee0 264),
  ("__tanhf", .absent),
  ("acoshf", .plain v2_2_5 350 0x16180 49),
  ("__acoshf", .absent),
  ("asinhf", .plain v2_2_5 188 0x3f2b0 377),
  ("__asinhf", .absent),
  ("atanhf", .plain v2_2_5 24 0x162f0 71),
  ("__atanhf", .absent),
  ("expf", .ifunc v2_27 1032),
  ("__expf", .absent),
  ("frexpf", .plain v2_2_5 963 0x41a40 107),
  ("__frexpf", .absent),
  ("ldexpf", .plain v2_2_5 926 0x41ac0 117),
  ("__ldexpf", .absent),
  ("logf", .ifunc v2_27 922),
  ("__logf", .absent),
  ("log10f", .plain v2_2_5 58 0x16900 113),
  ("__log10f", .absent),
  ("modff", .plain v2_2_5 960 0x418c0 151),
  ("__modff", .absent),
  ("expm1f", .plain v2_2_5 239 0x40260 945),
  ("__expm1f", .absent),
  ("log1pf", .plain v2_2_5 196 0x47760 57),
  ("__log1pf", .absent),
  ("logbf", .plain v2_2_5 1053 0x40980 88),
  ("__logbf", .absent),
  ("exp2f", .ifunc v2_27 1167),
  ("__exp2f", .absent),
  ("log2f", .ifunc v2_27 343),
  ("__log2f", .absent),
  ("powf", .ifunc v2_27 1112),
  ("__powf", .absent),
  ("sqrtf", .plain v2_2_5 468 0x16da0 41),
  ("__sqrtf", .absent),
  ("hypotf", .plain v2_35 1109 0x3a810 186),
  ("__hypotf", .absent),
  ("cbrtf", .plain v2_2_5 971 0x3f6a0 342),
  ("__cbrtf", .absent),
  ("ceilf", .ifunc v2_2_5 166),
  ("__ceilf", .absent),
  ("fabsf", .plain v2_2_5 397 0x40620 8),
  ("__fabsf", .absent),
  ("floorf", .ifunc v2_2_5 90),
  ("__floorf", .absent),
  ("fmodf", .plain v2_2_5 1117 0x164a0 75),
  ("__fmodf", .absent),
  ("isinff", .absent),
  ("finitef", .plain v2_2_5 819 0x41880 18),
  ("dremf", .plain v2_2_5 1055 0x16b40 82),
  ("__dremf", .absent),
  ("significandf", .plain v2_2_5 617 0x47690 40),
  ("__significandf", .absent),
  ("copysignf", .plain v2_2_5 1170 0x418a0 24),
  ("__copysignf", .absent),
  ("nanf", .plain v2_2_5 1173 0x47610 9),
  ("__nanf", .absent),
  ("isnanf", .absent),
  ("j0f", .plain v2_2_5 115 0x16570 64),
  ("__j0f", .absent),
  ("j1f", .plain v2_2_5 152 0x16670 64),
  ("__j1f", .absent),
  ("jnf", .plain v2_2_5 177 0x16770 75),
  ("__jnf", .absent),
  ("y0f", .plain v2_2_5 636 0x165b0 184),
  ("__y0f", .absent),
  ("y1f", .plain v2_2_5 681 0x166b0 184),
  ("__y1f", .absent),
  ("ynf", .plain v2_2_5 699 0x167c0 180),
  ("__ynf", .absent),
  ("erff", .plain v2_2_5 1146 0x3f860 1269),
  ("__erff", .absent),
  ("erfcf", .plain v2_2_5 859 0x3fd60 1276),
  ("__erfcf", .absent),
  ("lgammaf", .plain v2_23 271 0x17090 223),
  ("__lgammaf", .absent),
  ("tgammaf", .plain v2_2_5 390 0x16dd0 495),
  ("__tgammaf", .absent),
  ("gammaf", .plain v2_2_5 894 0x171e0 361),
  ("__gammaf", .absent),
  ("lgammaf_r", .plain v2_2_5 901 0x16fc0 207),
  ("__lgammaf_r", .absent),
  ("rintf", .ifunc v2_2_5 826),
  ("__rintf", .absent),
  ("nextafterf", .plain v2_2_5 1018 0x409e0 212),
  ("__nextafterf", .absent),
  ("remainderf", .plain v2_2_5 378 0x16b40 82),
  ("__remainderf", .absent),
  ("scalbnf", .plain v2_2_5 607 0x41ac0 117),
  ("__scalbnf", .absent),
  ("ilogbf", .plain v2_2_5 1192 0x476c0 60),
  ("__ilogbf", .absent),
  ("scalblnf", .plain v2_2_5 836 0x477a0 117),
  ("__scalblnf", .absent),
  ("nearbyintf", .ifunc v2_2_5 851),
  ("__nearbyintf", .absent),
  ("roundf", .plain v2_2_5 590 0x41390 109),
  ("__roundf", .absent),
  ("truncf", .ifunc v2_2_5 1136),
  ("__truncf", .absent),
  ("remquof", .plain v2_2_5 928 0x41060 459),
  ("__remquof", .absent),
  ("lrintf", .plain v2_2_5 808 0x415d0 6),
  ("__lrintf", .absent),
  ("llrintf", .plain v2_2_5 957 0x415d0 6),
  ("__llrintf", .absent),
  ("lroundf", .plain v2_2_5 733 0x415e0 140),
  ("__lroundf", .absent),
  ("llroundf", .plain v2_2_5 986 0x41670 140),
  ("__llroundf", .absent),
  ("fdimf", .plain v2_2_5 323 0x47500 81),
  ("__fdimf", .absent),
  ("fmaxf", .plain v2_2_5 312 0x47590 58),
  ("__fmaxf", .absent),
  ("fminf", .plain v2_2_5 809 0x475d0 58),
  ("__fminf", .absent),
  ("fmaf", .ifunc v2_2_5 554),
  ("__fmaf", .absent),
  ("scalbf", .plain v2_2_5 999 0x16c60 224),
  ("__scalbf", .absent)]

/-- The code of `__fpclassify` (`.dynsym` entry 810, `__fpclassify@@GLIBC_2.2.5`): 69 bytes at `0x30bf0`. -/
def fpclassifyBytes : List (BitVec 8) :=
  [0x66, 0x48, 0x0F, 0x7E, 0xC2, 0x48, 0x89, 0xD0, 0x48, 0xC1, 0xE8, 0x20, 0x89, 0xC1, 0x25, 0x00,
    0x00, 0xF0, 0x7F, 0x81, 0xE1, 0xFF, 0xFF, 0x0F, 0x00, 0x09, 0xCA, 0xB9, 0x02, 0x00, 0x00, 0x00,
    0x89, 0xD6, 0x09, 0xC6, 0x74, 0x1C, 0xB9, 0x03, 0x00, 0x00, 0x00, 0x85, 0xC0, 0x74, 0x13, 0xB9,
    0x04, 0x00, 0x00, 0x00, 0x3D, 0x00, 0x00, 0xF0, 0x7F, 0x75, 0x07, 0x31, 0xC9, 0x85, 0xD2, 0x0F,
    0x94, 0xC1, 0x89, 0xC8, 0xC3]

/-- The code of `__signbit` (`.dynsym` entry 208, `__signbit@@GLIBC_2.2.5`): 10 bytes at `0x32c70`. -/
def signbitBytes : List (BitVec 8) :=
  [0x66, 0x0F, 0xD7, 0xC0, 0x25, 0x80, 0x00, 0x00, 0x00, 0xC3]

/-- The code of `__finite` (`.dynsym` entry 382, `__finite@@GLIBC_2.2.5`): 26 bytes at `0x32980`. -/
def finiteInternalBytes : List (BitVec 8) :=
  [0x48, 0xBA, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF0, 0x7F, 0x66, 0x48, 0x0F, 0x7E, 0xC0, 0x48,
    0x21, 0xD0, 0x48, 0x29, 0xD0, 0x48, 0xC1, 0xE8, 0x3F, 0xC3]

/-- The code of `finite` (`.dynsym` entry 199, `finite@@GLIBC_2.2.5`): 26 bytes at `0x32980`. -/
def finiteBytes : List (BitVec 8) :=
  [0x48, 0xBA, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF0, 0x7F, 0x66, 0x48, 0x0F, 0x7E, 0xC0, 0x48,
    0x21, 0xD0, 0x48, 0x29, 0xD0, 0x48, 0xC1, 0xE8, 0x3F, 0xC3]

/-- The code of `round` (`.dynsym` entry 107, `round@@GLIBC_2.2.5`): 142 bytes at `0x311c0`. -/
def roundBytes : List (BitVec 8) :=
  [0x66, 0x48, 0x0F, 0x7E, 0xC0, 0x48, 0x89, 0xC1, 0x48, 0x89, 0xC2, 0x48, 0xC1, 0xF9, 0x34, 0x81,
    0xE1, 0xFF, 0x07, 0x00, 0x00, 0x48, 0x81, 0xE9, 0xFF, 0x03, 0x00, 0x00, 0x48, 0x83, 0xF9, 0x33,
    0x7F, 0x5E, 0x48, 0x85, 0xC9, 0x78, 0x31, 0x48, 0xBE, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x0F,
    0x00, 0x48, 0xD3, 0xEE, 0x48, 0x85, 0xF0, 0x74, 0x1B, 0x48, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x08, 0x00, 0x48, 0xF7, 0xD6, 0x48, 0xD3, 0xE8, 0x48, 0x01, 0xD0, 0x48, 0x21, 0xF0, 0x66,
    0x48, 0x0F, 0x6E, 0xC0, 0xC3, 0x0F, 0x1F, 0x00, 0x48, 0xB8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x48, 0x21, 0xD0, 0x48, 0x83, 0xF9, 0xFF, 0x75, 0xE4, 0x48, 0xBA, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0xF0, 0x3F, 0x48, 0x09, 0xD0, 0xEB, 0xD5, 0x66, 0x0F, 0x1F, 0x44, 0x00, 0x00,
    0x48, 0x81, 0xF9, 0x00, 0x04, 0x00, 0x00, 0x75, 0xCB, 0xF2, 0x0F, 0x58, 0xC0, 0xC3]

/-- The code of `lrint` (`.dynsym` entry 1135, `lrint@@GLIBC_2.2.5`): 6 bytes at `0x32760`. -/
def lrintBytes : List (BitVec 8) :=
  [0xF2, 0x48, 0x0F, 0x2D, 0xC0, 0xC3]

/-- The code of `llrint` (`.dynsym` entry 1119, `llrint@@GLIBC_2.2.5`): 6 bytes at `0x32760`. -/
def llrintBytes : List (BitVec 8) :=
  [0xF2, 0x48, 0x0F, 0x2D, 0xC0, 0xC3]

/-- The code of `lrintf` (`.dynsym` entry 808, `lrintf@@GLIBC_2.2.5`): 6 bytes at `0x415d0`. -/
def lrintfBytes : List (BitVec 8) :=
  [0xF3, 0x48, 0x0F, 0x2D, 0xC0, 0xC3]

/-- The code of `llrintf` (`.dynsym` entry 957, `llrintf@@GLIBC_2.2.5`): 6 bytes at `0x415d0`. -/
def llrintfBytes : List (BitVec 8) :=
  [0xF3, 0x48, 0x0F, 0x2D, 0xC0, 0xC3]

/-- The code of `fmax` (`.dynsym` entry 578, `fmax@@GLIBC_2.2.5`): 61 bytes at `0x38e30`. -/
def fmaxBytes : List (BitVec 8) :=
  [0x66, 0x0F, 0x2E, 0xC8, 0x7A, 0x06, 0xF2, 0x0F, 0x5F, 0xC1, 0xEB, 0x30, 0x66, 0x0F, 0x2E, 0xC9,
    0x7A, 0x12, 0xF2, 0x0F, 0x11, 0x44, 0x24, 0xF8, 0xF6, 0x44, 0x24, 0xFE, 0x08, 0x74, 0x19, 0xF2,
    0x0F, 0x10, 0xC1, 0xC3, 0x66, 0x0F, 0x2E, 0xC0, 0x7A, 0x0E, 0xF2, 0x0F, 0x11, 0x4C, 0x24, 0xF8,
    0xF6, 0x44, 0x24, 0xFE, 0x08, 0x74, 0x01, 0xC3, 0xF2, 0x0F, 0x58, 0xC1, 0xC3]

/-- The code of `fmin` (`.dynsym` entry 877, `fmin@@GLIBC_2.2.5`): 61 bytes at `0x38e70`. -/
def fminBytes : List (BitVec 8) :=
  [0x66, 0x0F, 0x2E, 0xC8, 0x7A, 0x06, 0xF2, 0x0F, 0x5D, 0xC1, 0xEB, 0x30, 0x66, 0x0F, 0x2E, 0xC9,
    0x7A, 0x12, 0xF2, 0x0F, 0x11, 0x44, 0x24, 0xF8, 0xF6, 0x44, 0x24, 0xFE, 0x08, 0x74, 0x19, 0xF2,
    0x0F, 0x10, 0xC1, 0xC3, 0x66, 0x0F, 0x2E, 0xC0, 0x7A, 0x0E, 0xF2, 0x0F, 0x11, 0x4C, 0x24, 0xF8,
    0xF6, 0x44, 0x24, 0xFE, 0x08, 0x74, 0x01, 0xC3, 0xF2, 0x0F, 0x58, 0xC1, 0xC3]

end Silmaril.Elf.Abi.Libm

end
