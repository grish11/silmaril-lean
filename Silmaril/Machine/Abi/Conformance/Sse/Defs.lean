module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.X86.Str9L.Thms
public import Silmaril.X86.Sep.Plan.Defs
import Silmaril.Proofs.Machine.Abi.Conformance.Sse.Bits

/-!
# `Mach.str9L`: a conformance machine with SSE state

**`Mach.str9L F exts`** is the tower machine `Str9L.isa F exts` (`Str9X`'s integer, string,
direction-flag, SSE-integer, AVX2-integer and x87 layers; MXCSR; the lanes `exts` of the
feature-parametric machine on a processor with features `F`) as a conformance machine
(`Conformance.Mach`). The scalar SSE/SSE2 row (`Sse.Add`) uses `F = baseline64` (x87, SSE,
SSE2: the x86-64 baseline) and `exts = Features.sseExts` (the legacy-encoded SSE/SSE2 lanes,
`floatExt` first).

**State.** `SState` is a tower state `l : Str9L.LState` and the parts of the FFI vector and x87
fields the tower does not hold:
* `vup i`: for `i < 16`, bits 511:256 of vector register `i` (its low 256 bits are ignored);
  for `i ≥ 16`, the whole register. The tower holds bits 255:0 of YMM0–15 (`xmm`, `hi`);
* `x87up i`: the x87 entry `i ≥ 8` (lower entries are ignored). The tower holds the eight x87
  registers.
Every step of `Mach.str9L` is a step of `Str9L.isa F exts` on `l` with `vup` and `x87up`
unchanged (`isa`, `Thms.str9L_step`). So bits 511:256 and registers 16–31 are **kept by every
step**, as legacy SSE encodings keep them on hardware. A VEX-encoded form (`Str9V`'s, or the
`Avx.ext` lane's if `exts` lists it) zeroes bits 255:128 in `l` but keeps `vup`: on a processor
with AVX-512 state, where VEX forms zero bits 511:256 too, such a step is not the hardware's.
The row's code has none; a row with VEX code should use a processor without AVX-512 (`F` with
no AVX-512 feature), where those bits do not exist.

**Modelled and carried** (`models`): `.machine` (core and memory), `.vectors` (the **whole**
field: all indices, all 512 bits; `vecOf`), `.x87` (the whole field: ST(i) for `i < 8`, by the
tower's TOP; `x87up` above), `.direction` (the tower's DF), `.mxcsr` (the tower's MXCSR) and
`.x87Control` (the tower's x87 control word). **Carried**: `.x87Mode` (the tower has no
MMX/x87 mode bit: a form that switches the mode on hardware, an MMX form or `emms`, would be
unfaithful for this field; the row's code has none) and `.fsBase` (the FFI copy of
the thread pointer: modelling it as the core's FS base would leave FFI states where the two
differ without a completion, `Admit.fsCoherent` relates them at entry, and `Good.fsBase` reads
the core's).

**Completions** (`Fills`): every `SState` that agrees with the FFI state on the modelled fields
(`Mach.FillsAll`, `Thms.str9L_fillsAll`). Whatever the modelled fields do not fix is
**arbitrary** in a completion: the time-stamp oracle `tsc` (a **per-read stream**: `rdtsc`
returns `tsc 0` and keeps `fun k => tsc (k + 1)`, so two reads in one run may differ; it is not
one constant per run), the CET assumption `cetOff`, the x87 status word beyond the TOP that
places ST(i), the x87 tag word, and the ignored parts of `vup` and `x87up`. No fixed oracle or
profile is assumed. `fill s tsc cetOff` is the completion with a given oracle and CET flag
(`Sep.Plan.ffiXState s` for the integer state and the XMM file, TOP = 0).
-/

@[expose] public section

namespace Silmaril.Machine.Abi.Conformance.Sse

open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (Word XReg)
open Silmaril.X86.Sep.Plan (ffiXState xregOfIdx)

/-- **The state of `Mach.str9L`**: a tower state and the hidden parts of the FFI vector and x87
fields. -/
structure SState where
  /-- The tower state. -/
  l : Silmaril.X86.Str9L.LState
  /-- Bits 511:256 of vector registers 0–15 (bits 255:0 ignored), and registers 16 on. -/
  vup : Nat → BitVec 512
  /-- x87 entries 8 on (entries 0–7 ignored). -/
  x87up : Nat → BitVec 80

/-- **Vector register `i` of a machine state**: for `i < 16`, bits 511:256 from `vup`, bits
255:128 and 127:0 from the tower (`hi`, `xmm`); above, `vup`. -/
def vecOf (x : SState) (i : Nat) : BitVec 512 :=
  if i < 16 then
    ((x.vup i).extractLsb' 256 256 ++ (x.l.hi (xregOfIdx i) ++ x.l.xmm (xregOfIdx i)) :
      BitVec 512)
  else x.vup i

/-- **x87 entry `i` of a machine state**: ST(i) of the tower for `i < 8`, `x87up` above. -/
def x87Of (x : SState) (i : Nat) : BitVec 80 :=
  if h : i < 8 then x.l.x.fpu.st ⟨i, h⟩ else x.x87up i

/-- **The fields `Mach.str9L` models**: all but x87 mode and the FFI thread pointer. -/
def models : FfiField → Bool
  | .machine | .vectors | .x87 | .direction | .mxcsr | .x87Control => true
  | .x87Mode | .fsBase => false

/-- **The FFI state a machine state stands for**, on the modelled fields (`x87Mode` and
`fsBase` are placeholders `store` never reads). -/
def view (x : SState) : Ffi.State where
  machine := x.l.x.d.v.g.x.m
  vectors := vecOf x
  x87 := x87Of x
  direction := x.l.x.d.df
  x87Mode := true
  mxcsr := x.l.mxcsr.bits
  x87Control := x.l.x.fpu.control
  fsBase := 0

/-- **The admissible completions**: every machine state agreeing with `s` on the modelled
fields. -/
def Fills (s : Ffi.State) (x : SState) : Prop :=
  ∀ f, models f = true → f.Agree (view x) s

/-- The x87 state of a completion: ST(i) = entry `i` (TOP = 0), the FFI control word; status
otherwise and tags zero. -/
def fpuOf (s : Ffi.State) : Silmaril.X86.Features.X87 :=
  ⟨fun j => s.x87 j.val, 0, s.x87Control, 0⟩

/-- **The completion of `s` with time-stamp stream `tsc` and CET flag `cetOff`**: the integer
state and XMM file of `Sep.Plan.ffiXState s`, bits 255:128 of each vector register, DF, the
x87 state, MXCSR, and the vector and x87 fields as the hidden parts. -/
def fill (s : Ffi.State) (tsc : Nat → Word) (cetOff : Bool) : SState :=
  ⟨⟨⟨⟨⟨⟨ffiXState s, tsc, cetOff⟩, fun r => (s.vectors r.toBitVec.toNat).extractLsb' 128 128⟩,
      s.direction⟩, fpuOf s⟩, ⟨s.mxcsr⟩⟩, s.vectors, s.x87⟩

theorem fill_fills (s : Ffi.State) (tsc : Nat → Word) (cetOff : Bool) :
    Fills s (fill s tsc cetOff) := fun f hf => by
  cases f
  case vectors => exact funext (Silmaril.Proofs.Machine.Abi.Conformance.Sse.vec_split s.vectors)
  case x87 => exact funext (Silmaril.Proofs.Machine.Abi.Conformance.Sse.x87_split s.x87 _)
  case x87Mode | fsBase => cases hf
  all_goals rfl

/-- **The machine on `SState`**: `Str9L.isa F exts` on the tower state, the hidden parts
unchanged. -/
@[reducible] def isa (F : Silmaril.X86.Features.FeatureSet)
    (exts : List Silmaril.X86.Features.Extension) : Silmaril.X86.SegVC.Isa SState where
  Instr := Silmaril.X86.Str9FsX.Instr
  instDecEq := inferInstance
  decode := Silmaril.X86.Str9D.decode
  exec := Silmaril.X86.Str9FsX.exec
  core x := x.l.core
  mem x := x.l.memory
  upd x c m := { x with l := (Silmaril.X86.Str9L.isa F exts).upd x.l c m }
  core_upd _ _ _ := rfl
  mem_upd _ _ _ := rfl
  upd_self _ := rfl
  ok _ _ := True
  live _ := True
  step x := (Silmaril.X86.Str9L.step F exts x.l).map fun l => { x with l }
  live_step _ _ := trivial
  step_of hlive hl hrip hfit hdec hx hok := by
    have h : Silmaril.X86.Str9L.step F exts _ = some _ :=
      (Silmaril.X86.Str9L.isa F exts).step_of trivial hl hrip hfit hdec hx trivial
    simp only [h, Option.map_some]

end Silmaril.Machine.Abi.Conformance.Sse

namespace Silmaril.Machine.Abi.Conformance

/-- **`Str9L` as a conformance machine** (`Sse.isa F exts` on `Sse.SState`): it models the
machine, the whole vector field, the whole x87 field, the direction flag, MXCSR and the x87
control word, and carries x87 mode and the FFI thread pointer (`Sse.models`); its completions
are all states that fit (`Sse.Fills`), with any time-stamp stream and CET flag. -/
def Mach.str9L (F : Silmaril.X86.Features.FeatureSet)
    (exts : List Silmaril.X86.Features.Extension) : Mach where
  σ := Sse.SState
  isa := Sse.isa F exts
  models := Sse.models
  models_machine := rfl
  view := Sse.view
  machine_view _ := rfl
  Fills := Sse.Fills
  fills_agree h := h
  fills_total s := ⟨Sse.fill s (fun _ => 0) false, Sse.fill_fills s _ _⟩

end Silmaril.Machine.Abi.Conformance

end
