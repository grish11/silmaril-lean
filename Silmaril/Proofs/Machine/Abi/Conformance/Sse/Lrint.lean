module

public import Silmaril.Machine.Abi.Conformance.Sse.Lrint.Defs
public import Silmaril.Machine.Abi.Conformance.Thms
public import Silmaril.Machine.Abi.Conformance.Sse.Thms
public import Silmaril.Machine.Abi.SystemV.Scalar.Thms
public import Silmaril.Proofs.Machine.Abi.Conformance.Basic
public import Silmaril.X86.Spec.Ensures
public import Silmaril.X86.Float.Semantics

/-!
# `long lrint(double)` as `cvtsd2si %xmm0, %rax; ret` on `Mach.str9L`, at any base: proofs

* the witness: the code at `base` (below `2^47`), `rsp = 2^47 + 0x8ff8` with the return address
  `2^47 + 0x2000` (above every byte of the image), one region mapping every address, the
  argument in the low half of vector register 0, MXCSR `0x1F80` (`st`);
* the run: from every completion of every admitted call, `cvtsd2si` (the `floatExt` lane:
  `Str9L.step_of_listed_float`) then `ret`, the second state the first return (`firstReturn`);
* the row (`conforms`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.Sse.Lrint

open Silmaril.X86 (State MState Word Byte Reg XReg)
open Silmaril.Process (Memory Region)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.Sse
open Silmaril.Machine.Abi.Conformance.Sse.Lrint

/-! ## The witness -/

def allRegion : Region := ⟨0, 2 ^ 64, ⟨true, true, true⟩⟩

/-- The stack pointer of the witness: above every load base the rows admit. -/
def rsp0 : Word := 0x800000008ff8

def retAt : Word := 0x800000002000

def retEnc : List Byte := Silmaril.Machine.LittleEndian.encodeWords [retAt]

def mem (base : Word) : Memory :=
  ⟨[allRegion], Memory.install (Memory.install ∅ rsp0.toNat retEnc) base.toNat bytes⟩

def core0 (base : Word) : State :=
  ⟨fun r => match r with | .rsp => rsp0 | _ => 0, base, ⟨none, none, none, none, none, none⟩, 0⟩

/-- `a` in the low half of vector register 0. -/
def vecs (a : BitVec 64) (i : Nat) : BitVec 512 :=
  if i = 0 then a.setWidth 512 else 0

/-- **The witness call** `lrint(a)` of the code at `base`. -/
def st (base : Word) (a : BitVec 64) : Ffi.State :=
  ⟨⟨core0 base, mem base⟩, vecs a, fun _ => 0, false, true, 0x1F80, 0x037F, 0⟩

theorem permits_all (base : Word) (acc) (a : Nat) (ha : a < 2 ^ 64) :
    (mem base).permits acc a = true := by
  have : a < 18446744073709551616 := ha
  cases acc <;>
    simp [Memory.permits, mem, allRegion, Silmaril.Process.Region.Contains,
      Silmaril.Process.Permissions.allows, this]

theorem permitted (base : Word) (acc) (a n : Nat) (h : a + n < 2 ^ 64) :
    (mem base).Permitted acc a n := by
  simp only [Memory.Permitted, Memory.checkSpan_iff]
  exact ⟨by simp only [Silmaril.Process.addressLimit]; omega,
    by simp only [Silmaril.Process.addressLimit]; omega,
    fun i _ => permits_all base acc _ (by omega)⟩

theorem bytes_length : bytes.length = 6 := rfl

theorem loaded {base : Word} (hb : base.toNat + 6 ≤ 2 ^ 47) :
    Silmaril.X86.Ext.Loaded (mem base) base bytes :=
  Memory.readWith_eq _ _ _ bytes (permitted base _ _ _ (by rw [bytes_length]; omega))
    fun i hi => Memory.install_get _ _ _ _ hi

theorem ret_read {base : Word} (hb : base.toNat + 6 ≤ 2 ^ 47) :
    (mem base).readBytes rsp0.toNat 8 = some retEnc := by
  refine Memory.readWith_eq _ _ _ retEnc (permitted base _ _ _ (by decide)) fun i hi => ?_
  simp only [retEnc, Silmaril.Machine.LittleEndian.encodeWords_length, List.length_cons,
    List.length_nil] at hi
  show (Memory.install _ _ _).get? _ = _
  rw [Memory.install_outside _ _ _ _ (by
    right; rw [bytes_length]; show base.toNat + 6 ≤ 0x800000008ff8 + i; omega)]
  exact Memory.install_get _ _ _ _ (by simp [retEnc]; omega)

theorem retOf_st {base : Word} (hb : base.toNat + 6 ≤ 2 ^ 47) (a : BitVec 64) :
    Silmaril.X86.FnContract.retOf (st base a).machine.core (st base a).machine.memory = retAt :=
  Silmaril.X86.FnContract.retOf_of_readBytes (ret_read hb)

/-- `sysvScalar`'s plan for `proto`: XMM0 in, RAX out, no stack. -/
theorem plan_eq : Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result =
    ⟨[⟨Silmaril.Machine.Abi.SystemV.Scalar.Kind.double.object, [⟨0, 8, .vector 0 0⟩], none⟩],
      .direct [⟨0, 8, .gp .rax⟩], 0, 16, 0, 1, none⟩ := by decide

theorem argArea_eq : abi.argArea proto = 0 := by decide

theorem low_vecs (v : BitVec 64) : (v.setWidth 512).setWidth 64 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

/-- The C argument `a`. -/
def args (a : BitVec 64) : abi.V.Args proto := (a, PUnit.unit)

theorem entry_st {base : Word} (hb : base.toNat + 6 ≤ 2 ^ 47) (a : BitVec 64) :
    abi.conv.Entry proto (args a) (st base a) := by
  refine ⟨retAt, rfl, ?_, ?_, ?_, ret_read hb, ?_, rfl, rfl, ?_⟩
  · show Ffi.ArgumentsAt (st base a)
      (proto.args.map Silmaril.Machine.Abi.SystemV.Scalar.Arg.spec) (args a)
      (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).arguments
    rw [plan_eq]
    exact ⟨⟨rfl, _, rfl, (vector_chunk_iff _ (by decide) _).2 (low_vecs a)⟩, trivial⟩
  · show (rsp0.toNat + 8) %
      (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).stackAlign = 0
    rw [plan_eq]; decide
  · show rsp0.toNat + 8 +
      (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).stackSize ≤ 2 ^ 64
    rw [plan_eq]; decide
  · rfl
  · show ∀ count,
      (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).variadicAL =
        some count → _
    rw [plan_eq]
    exact fun _ h => nomatch h

theorem toNat_add_lt {base : Word} (hb : base.toNat + 6 ≤ 2 ^ 47) {o : Nat} (ho : o < 6) :
    (base + BitVec.ofNat 64 o).toNat = base.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : o < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

theorem placed {base : Word} (image : List (Word × Nat)) (hb : base.toNat + 6 ≤ 2 ^ 47)
    (a : BitVec 64) : Placed (code base image) (st base a) := by
  refine ⟨loaded hb, ?_, (fun _ h => nomatch h), fun o ho => ?_⟩
  · show base = base + BitVec.ofNat 64 0
    simp
  · change o < 6 at ho
    rw [retOf_st hb]
    intro h
    have := congrArg BitVec.toNat h
    change retAt.toNat = (base + BitVec.ofNat 64 o).toNat at this
    rw [toNat_add_lt hb ho, show retAt.toNat = 0x800000002000 from rfl] at this
    omega

theorem stack {base : Word} {image : List (Word × Nat)} (hb : base.toNat + 6 ≤ 2 ^ 47)
    (hi : ∀ r ∈ image, r.1.toNat + r.2 ≤ 2 ^ 47) (a : BitVec 64) :
    Stack abi proto (code base image) 0 (fun _ => False) (st base a) := by
  have hsp : sp (st base a) = 0x800000008ff8 := rfl
  have hown : ∀ x, ¬ abi.owned proto (st base a) x := by
    intro x h
    have h0 : sretBytes proto = 0 := by decide
    simp only [abi, AbiDef.defaultEnv, sysvScalar, h0, Nat.add_zero] at h
    omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, (fun _ h => nomatch h), ?_, (fun _ h => h.elim),
    (fun x h => absurd h (hown x)), (fun x h => absurd h (hown x)),
    (fun x h => absurd h (hown x)), (fun x h => absurd h (hown x)), (fun x h => absurd h (hown x)),
    (fun x h => absurd h (hown x)), (fun x h => absurd h (hown x))⟩
  · rw [argArea_eq, hsp]; decide
  · rw [argArea_eq, hsp]; exact permitted _ _ _ _ (by decide)
  · rw [argArea_eq, hsp]; exact permitted _ _ _ _ (by decide)
  · left
    show base.toNat + 6 ≤ sp (st base a) - 0
    rw [hsp]; omega
  · intro r hr
    left
    show r.1.toNat + r.2 ≤ sp (st base a) - 0
    rw [hsp]
    have := hi r hr
    omega

/-- **The admitted call `lrint(a)`** on every machine whose states are all live. -/
theorem admit_st {M : Mach} (hl : ∀ x, M.isa.live x) {base : Word} {image : List (Word × Nat)}
    (hb : base.toNat + 6 ≤ 2 ^ 47) (hi : ∀ r ∈ image, r.1.toNat + r.2 ≤ 2 ^ 47)
    (S : CallSpec abi.V proto) (hS : S.objects = fun _ _ _ => False) (a : BitVec 64) :
    Admit abi M proto (code base image) 0 S (args a) (st base a) := by
  refine ⟨fun x _ => hl x, entry_st hb a, ⟨trivial, rfl⟩, placed image hb a, ?_, rfl⟩
  rw [hS]
  exact stack hb hi a

/-! ## What an admitted call fixes -/

theorem entry_facts {M : Mach} {c : Code} {S : CallSpec abi.V proto} {a : abi.V.Args proto}
    {s : Ffi.State} (ad : Admit abi M proto c 0 S a s) :
    ∃ exit, s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [exit]) ∧
      s.direction = false ∧ s.x87Mode = true ∧
      Ffi.ChunksAt s (Ffi.bytesOfNat a.1.toNat 0 8) [⟨0, 8, .vector 0 0⟩] ∧
      s.mxcsr = 0x1F80 := by
  obtain ⟨exit, e⟩ := ad.entry
  have hargs := e.argumentsAt
  change Ffi.ArgumentsAt s (proto.args.map Silmaril.Machine.Abi.SystemV.Scalar.Arg.spec) a
    (Silmaril.Machine.Abi.SystemV.Scalar.scalarPlan proto.args proto.result).arguments at hargs
  rw [plan_eq] at hargs
  obtain ⟨⟨-, b0, e0, c0⟩, -⟩ := hargs
  change b0 = Ffi.bytesOfNat a.1.toNat 0 8 at e0
  subst e0
  exact ⟨exit, e.returnAddress, e.direction, e.x87Mode, c0, ad.env.2⟩

/-! ## The run -/

/-- `cvtsd2si %xmm0, %rax`. -/
abbrev cvt : Silmaril.X86.Float.Instr := .cvtToInt .double .w64 .rax (.reg .xmm0)

theorem laneBad_cvt : Silmaril.X86.Str9L.laneBad [0xF2, 0x48, 0x0F, 0x2D, 0xC0] = true ∧
    Silmaril.X86.Float.decode [0xF2, 0x48, 0x0F, 0x2D, 0xC0] = some (cvt, 5) := by decide

/-- The scalar SSE state of a machine state. -/
def fsOf (x : SState) : Silmaril.X86.Float.State := ⟨x.l.core, x.l.x.d.v.g.x.xmm, x.l.mxcsr⟩

/-- The operand: the low binary64 lane of XMM0. -/
def argOf (x : SState) : Numeric.Float.Bits Silmaril.X86.Float.Precision.double.fmt :=
  Silmaril.X86.Float.lane .double ((fsOf x).readX .xmm0)

/-- The integer `cvtsd2si` computes. -/
def valOf (x : SState) : BitVec 64 :=
  (Silmaril.X86.Float.Scalar.toInt (fsOf x).mxcsr .double .w64 (fsOf x).mxcsr.rounding
    (argOf x)).value

/-- The scalar state after `cvtsd2si` with every exception masked. -/
def cvtT (x : SState) : Silmaril.X86.Float.State :=
  Silmaril.X86.Float.advance cvt
    { (fsOf x).writeGpr .rax (valOf x) with
      mxcsr := (fsOf x).mxcsr.record (Silmaril.X86.Float.Scalar.toIntDetected (fsOf x).mxcsr
        .double .w64 (fsOf x).mxcsr.rounding (argOf x)).all }

theorem exec_cvt (x : SState) (hm : (fsOf x).mxcsr.AllMasked) :
    cvt.exec (fsOf x) x.l.memory = .commit (cvtT x) x.l.memory := by
  rw [Silmaril.X86.Float.exec_cvtToInt (p := .double) (y := argOf x) rfl,
    Silmaril.X86.Float.finish_of_allMasked _ _ _ hm]
  rfl

/-- The machine state after `cvtsd2si`. -/
def x1 (x : SState) : SState :=
  { x with l := ⟨⟨⟨⟨{ x.l.x.d.v.g with x := ⟨⟨(cvtT x).core, x.l.memory⟩, (cvtT x).xmm⟩ },
    x.l.x.d.v.hi⟩, x.l.x.d.df⟩, x.l.x.fpu⟩, (cvtT x).mxcsr⟩ }

theorem step_cvt {base : Word} {image : List (Word × Nat)} (x : SState)
    (hl : Silmaril.X86.Ext.Loaded x.l.memory (code base image).base bytes)
    (hrip : x.l.core.rip = (code base image).base) (hm : x.l.mxcsr.AllMasked) :
    mach.isa.step x = some (x1 x) := by
  show (Silmaril.X86.Str9L.step _ (Silmaril.X86.Features.floatExt :: _) x.l).map _ = _
  rw [Silmaril.X86.Str9L.step_of_listed_float (o := 0) (l := 5) hl
    (by rw [hrip]; simp) (by decide) (by decide) laneBad_cvt.1 laneBad_cvt.2 (by decide)
    (exec_cvt x hm)]
  rfl

theorem x1_rip (x : SState) : (x1 x).l.core.rip = x.l.core.rip + 5 := rfl

/-- `ret`, as `Str9D` decodes it. -/
abbrev retI : Silmaril.X86.Str9FsX.Instr :=
  .base (.str9 (.ext9 (.ext8 (.base .ret))))

/-- The core after `ret` to `exit`. -/
def retCore (c : State) (exit : Word) : State :=
  { c.write .rsp (c.read .rsp + 8#64) with rip := exit }

theorem retCore_read (c : State) (exit : Word) (r : Reg) :
    (retCore c exit).read r = (c.write .rsp (c.read .rsp + 8#64)).read r := rfl

/-- The machine state after `ret` to `exit`. -/
def x2 (x : SState) (exit : Word) : SState :=
  mach.isa.upd (x1 x) (retCore (x1 x).l.core exit) x.l.memory

theorem x1_rsp (x : SState) : (x1 x).l.core.read .rsp = x.l.core.read .rsp := by
  show ((fsOf x).writeGpr .rax (valOf x)).core.read .rsp = _
  exact Silmaril.X86.State.read_write_other _ _ _ _ (by decide)

theorem step_ret {base : Word} {image : List (Word × Nat)} (x : SState) (exit : Word)
    (hl : Silmaril.X86.Ext.Loaded x.l.memory (code base image).base bytes)
    (hrip : x.l.core.rip = (code base image).base)
    (hra : x.l.memory.readBytes (x.l.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit])) :
    mach.isa.step (x1 x) = some (x2 x exit) := by
  have hw : Silmaril.X86.Spec.WordAt x.l.memory ((x1 x).l.core.read .rsp) exit :=
    ⟨_, by rw [x1_rsp]; exact hra, by simp⟩
  refine mach.isa.step_of (s := x1 x) (o := 5) (l := 1) (i := retI) trivial hl
    (by show (x1 x).l.core.rip = _; rw [x1_rip, hrip]; rfl) (by decide) (by decide) ?_ trivial
  exact Silmaril.X86.Spec.exec_ret_eq hw

/-! ## Every completion of every admitted call -/

section Completion

variable {base : Word} {image : List (Word × Nat)} {S : CallSpec abi.V proto}
  {a : abi.V.Args proto} {s : Ffi.State} {x : SState}

theorem fills_m (hx : mach.Fills s x) : x.l.x.d.v.g.x.m = s.machine := hx .machine rfl

theorem fills_core (hx : mach.Fills s x) : x.l.core = s.machine.core := by
  show x.l.x.d.v.g.x.m.core = _; rw [fills_m hx]

theorem fills_mem (hx : mach.Fills s x) : x.l.memory = s.machine.memory := by
  show x.l.x.d.v.g.x.m.memory = _; rw [fills_m hx]

theorem masked (ad : Admit abi mach proto (code base image) 0 S a s) (hx : mach.Fills s x) :
    x.l.mxcsr.AllMasked := by
  obtain ⟨_, _, _, _, _, hm⟩ := entry_facts ad
  rw [Sse.fills_mxcsr hx, hm]
  exact Silmaril.X86.Float.MXCSR.reset_allMasked

theorem not_returned_of_rip {y : SState} (hy : y.l.core.rip = base + BitVec.ofNat 64 5 ∨
      y.l.core.rip = base + BitVec.ofNat 64 0)
    (ad : Admit abi mach proto (code base image) 0 S a s) (hx : mach.Fills s x) :
    ¬ Silmaril.X86.FnContract.Returned mach.isa x y := by
  intro h
  have hr : y.l.core.rip = Silmaril.X86.FnContract.retOf s.machine.core s.machine.memory := by
    have := h.1
    simp only [mach, Mach.str9L, Sse.isa] at this
    rw [this, fills_core hx, fills_mem hx]
  rcases hy with e | e
  · exact ad.placed.retOutside 5 (by show 5 < 6; decide) (hr.symm.trans e)
  · exact ad.placed.retOutside 0 (by show 0 < 6; decide) (hr.symm.trans e)

/-- **The first return**: `cvtsd2si` then `ret`, from every completion of every admitted call. -/
theorem firstReturn (ad : Admit abi mach proto (code base image) 0 S a s) (hx : mach.Fills s x)
    {exit : Word}
    (hra : s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit])) :
    Silmaril.X86.FnContract.FirstReturn mach.isa x (x2 x exit) := by
  have hl : Silmaril.X86.Ext.Loaded x.l.memory (code base image).base bytes := by
    rw [fills_mem hx]; exact ad.placed.loaded
  have hrip : x.l.core.rip = (code base image).base := by
    rw [fills_core hx, ad.placed.pc]; show base + BitVec.ofNat 64 0 = base; simp
  have hra' : x.l.memory.readBytes (x.l.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]) := by
    rw [fills_mem hx, fills_core hx]; exact hra
  refine ⟨.step (not_returned_of_rip (.inr (by rw [hrip]; simp; rfl)) ad hx)
    (step_cvt x hl hrip (masked ad hx))
    (.step (not_returned_of_rip (.inl (by rw [x1_rip, hrip]; rfl)) ad hx)
      (step_ret x exit hl hrip hra') (.refl _)), ?_, ?_⟩
  · show exit = Silmaril.X86.FnContract.retOf x.l.core x.l.memory
    exact (Silmaril.X86.FnContract.retOf_of_readBytes hra').symm
  · show (retCore (x1 x).l.core exit).read .rsp = x.l.core.read .rsp + 8#64
    rw [retCore_read, Silmaril.X86.State.read_write_same, x1_rsp]

/-- MXCSR's control bits are kept when status flags are ORed in. -/
theorem record_control (m : Silmaril.X86.Float.MXCSR) (e : Silmaril.X86.Float.Exceptions) :
    (m.record e).bits &&& 0xffc0 = m.bits &&& 0xffc0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Silmaril.X86.Float.MXCSR.record, BitVec.getLsbD_and, BitVec.getLsbD_or]
  by_cases h : 6 ≤ i
  · rw [Silmaril.X86.Float.Exceptions.toBits_getLsbD_of_ge e h, Bool.or_false]
  · have : (0xffc0 : BitVec 32).getLsbD i = false := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [this, Bool.and_false, Bool.and_false]

theorem lane_eq (v : BitVec 128) : Silmaril.X86.Float.lane .double v = v.setWidth 64 := by
  show v.extractLsb' 0 64 = v.setWidth 64
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  simp [hj]

/-- RAX after the run. -/
theorem x2_rax (x : SState) (exit : Word) :
    (retCore (x1 x).l.core exit).read .rax = valOf x := by
  rw [retCore_read, Silmaril.X86.State.read_write_other _ _ _ _ (by decide)]
  show ((fsOf x).writeGpr .rax (valOf x)).core.read .rax = _
  exact Silmaril.X86.State.read_write_same _ _ _

/-- **The result read back** is RAX. -/
theorem resultAt_rax (s t : Ffi.State) (r : BitVec 64) (h : t.machine.core.read .rax = r) :
    abi.conv.ResultAt proto s t r := by
  refine (Silmaril.Machine.Abi.SystemV.Scalar.resultAt_some {} [.scalar .double] .int64
    (by decide) s t r).2 ?_
  simp only [Silmaril.Machine.Abi.SystemV.Scalar.Kind.sse, Bool.false_eq_true, ↓reduceIte,
    Ffi.locationBytes, Silmaril.Machine.Abi.SystemV.Scalar.Kind.bytes,
    Silmaril.Machine.Abi.SystemV.Scalar.Kind.encode, Nat.reduceMul, Nat.le_refl, h]
  rw [BitVec.setWidth_eq]

/-- **A conforming return** from every completion. -/
theorem good (ad : Admit abi mach proto (code base image) 0 S a s) (hx : mach.Fills s x)
    {exit : Word}
    (hra : s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]))
    (hpost : ∀ t, S.post a s (toLong s.mxcsr a.1) t) :
    Good abi proto 0 S a s (mach.store s (x2 x exit)) := by
  obtain ⟨_, _, hdir, hmode, c0, -⟩ := entry_facts ad
  have hcore := fills_core hx
  refine ⟨⟨exit, hra, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩, ⟨_, ?_, hpost _⟩, ?_, ?_⟩
  · rfl
  · show (retCore (x1 x).l.core exit).read .rsp = s.machine.core.read .rsp + 8
    rw [retCore_read, Silmaril.X86.State.read_write_same, x1_rsp, ← hcore]
    rfl
  · intro r hr
    have hne : r ≠ .rsp ∧ r ≠ .rax := by
      simp only [Silmaril.X86.sysv64, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    show (retCore (x1 x).l.core exit).read r = s.machine.core.read r
    rw [retCore_read, Silmaril.X86.State.read_write_other _ _ _ _ hne.1, ← hcore]
    show ((fsOf x).writeGpr .rax (valOf x)).core.read r = _
    exact Silmaril.X86.State.read_write_other _ _ _ _ hne.2
  · show x.l.x.d.df = false
    have hd : x.l.x.d.df = s.direction := hx .direction rfl
    rw [hd, hdir]
  · exact hmode
  · show (x.l.mxcsr.record _).bits &&& 0xffc0 = s.mxcsr &&& 0xffc0
    have hm : x.l.mxcsr.bits = s.mxcsr := hx .mxcsr rfl
    rw [record_control, hm]
  · exact (hx .x87Control rfl : x.l.x.fpu.control = s.x87Control)
  · refine resultAt_rax s _ _ ?_
    show (retCore (x1 x).l.core exit).read .rax = _
    rw [x2_rax]
    show (Silmaril.X86.Float.Scalar.toInt x.l.mxcsr .double .w64 x.l.mxcsr.rounding
      (Silmaril.X86.Float.lane .double (x.l.xmm .xmm0))).value = _
    rw [lane_eq, Sse.fills_mxcsr hx,
      show x.l.xmm .xmm0 = x.l.xmm (Silmaril.X86.Sep.Plan.xregOfIdx 0) from rfl,
      Sse.entry_xmm (by decide) c0 hx]
    rfl
  · show s.machine.memory.WritesWithin x.l.memory _
    rw [fills_mem hx]
    exact Memory.WritesWithin.refl _ _
  · show (retCore (x1 x).l.core exit).fsBase = s.machine.core.fsBase
    rw [← hcore]; rfl

end Completion

/-! ## The row -/

/-- **`cvtsd2si %xmm0, %rax; ret` at `base` conforms to the default-environment subset of
`sysvScalar` as the `long (double)` function `f` of `hdr`** on `Mach.str9L`, in total mode,
with the result `toLong`, when the code and the image are below `2^47`. -/
theorem conforms {hdr : HeaderSrc} {f : String} (hd : Declares abi hdr f proto) {base : Word}
    {image : List (Word × Nat)} (hb : base.toNat + 6 ≤ 2 ^ 47)
    (hi : ∀ r ∈ image, r.1.toNat + r.2 ≤ 2 ^ 47) :
    Conforms abi mach .total hdr f proto (code base image) 0 spec := by
  refine ⟨hd, by show 0 + 6 ≤ 6; decide, ⟨args 0, st base 0, admit_st (fun _ => trivial) hb hi spec rfl 0,
      trivial⟩, fun a _ _ _ => ?_, fun a s ad _ x hx => ?_, fun _ a s ad _ x hx => ?_,
    fun a s ad _ t ht => ?_⟩
  · obtain ⟨a0, ⟨⟩⟩ := a
    exact ⟨st base a0, admit_st (fun _ => trivial) hb hi spec rfl a0, trivial,
      fun _ => Iff.rfl, fun _ h => h.elim⟩
  · obtain ⟨exit, hra, -⟩ := entry_facts ad
    exact Silmaril.Proofs.Machine.Abi.Conformance.noStuck_of_firstReturn (firstReturn ad hx hra)
  · obtain ⟨exit, hra, -⟩ := entry_facts ad
    exact ⟨_, _, firstReturn ad hx hra, rfl⟩
  · obtain ⟨x, hx, y, fr, rfl⟩ := ht
    obtain ⟨exit, hra, -⟩ := entry_facts ad
    rw [Silmaril.X86.FnContract.firstReturn_unique fr (firstReturn ad hx hra)]
    exact good ad hx hra (fun _ => rfl)

end Silmaril.Proofs.Machine.Abi.Conformance.Sse.Lrint

end
