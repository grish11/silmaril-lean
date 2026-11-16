module

public import Silmaril.Sim.SysV.Thms
public import Silmaril.Sim.X86.G.Thms
public import Silmaril.X86.AbiFunction.LeafArith.Thms
import Mathlib.Tactic.IntervalCases

/-!
# `bswap32_manual` from the pinned ELF, through the ISA → Wasm reduction

The function `bswap32_manual` of `examples/elf-ladder/01-leaf-arith` compiles (gcc 13.3 `-O2`)
to `mov %edi,%eax; bswap %eax; ret`, the five bytes `89 f8 0f c8 c3` at `0x401420` of the pinned
executable. This module proves its System V contract **from a Wasm proof**:

* `bswapProg`/`bswapCode`: the decoded body and the Wasm code the G simulator (`Silmaril.Sim.X86.G`) generates
  for it (`emitProg`, with the forms `mov r32, r32` and `bswap r32` added for this example);
* `bswap_wasm`: the Wasm problem (`WProblem`, about Wasm globals only) solved by `wpc` (`g_vc`);
* `bswap_xgoal`, **`bswap_sysv`**: the x86 System V statement on the bytes (`Ext.Returns` to the
  sentinel, `AbiEntry`/`AbiReturn`, `rax` = the C result), through the generic System V edge of `Silmaril.Sim.SysV`;
* **`bswap_in_elf`**: those bytes are what the pinned ELF loads at `0x401420` (`rx`), sliced from
  the existing binary tie `Pinned.leafArith_region`;
* `bswap32Spec_eq`: the ladder's C-level spec `Ladder.LeafArith.bswap32Spec` (shifts and masks,
  as in the C source) is silmaril's `byteSwap32`, so the result statement is literally the
  post of the existing `bswapSpec` (`Ladder.LeafArith.bswap32_manual_total`).
-/

@[expose] public section

namespace Silmaril.Sim.ElfVerify

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg State MState Word)
open Silmaril.Sim.X86.G Silmaril.Sim.SysV

/-- The body of `bswap32_manual`, decoded (`ret` is the wrapper's). -/
def bswapProg : XProg := [(.mov .d (.reg .rax) .rdi, 2), (.bswap .d .rax, 2)]

/-- The bytes of `bswap32_manual`, instruction by instruction, `ret` last. -/
def bswapBytes : List (List (BitVec 8)) := [[0x89, 0xf8], [0x0f, 0xc8], [0xc3]]

/-- The generated Wasm code of the body. -/
def bswapCode : List Instr :=
  mov32Code .rax .rdi ++ nextCode 2 ++ bswap32Code .rax ++ nextCode 2

theorem bswap_emit : emitProg bswapProg = some bswapCode := rfl

/-- Body spec: `rax = bswap32Val (rdi & 0xffffffff)`, every other register unchanged. -/
def BswapPost (R R' : Reg → Word) : Prop :=
  R' .rax = bswap32Val (R .rdi &&& 0xffffffff) ∧ ∀ r, r ≠ .rax → R' r = R r

/-- **The Wasm problem**, solved by the VC generator: no x86 in the statement or the proof. -/
theorem bswap_wasm {H : Type} {P : Profile} {host : HostSemantics H} :
    WProblem (H := H) P host bswapCode (fun _ => True) BswapPost := by
  intro s f R ⟨hl, hr, ⟨w, hw⟩, ⟨bc, hc⟩, ⟨bz, hz⟩, ⟨bs, hs⟩, ⟨bo, ho⟩⟩ _
  apply hwp_of_wpc (fun _ _ _ _ => True)
  g_vc [bswapCode, mov32Code, bswap32Code, Silmaril.Sim.X86.G.exec1_shl, Silmaril.Sim.X86.G.exec1_shru, hl, hr, hw, hc, hz, hs, ho,
    List.append_assoc]
  refine ⟨trivial, fun R' h => ⟨?_, fun r hr => ?_⟩⟩
  · have h' := h .rax
    simp only [ite_true, Option.some.injEq, val_i64_inj] at h'
    rw [← h']
    rfl
  · have h' := h r
    simp only [hr, ite_false, Option.some.injEq, val_i64_inj] at h'
    exact h'.symm

/-- The ladder's C spec (`(x >> 24) | ((x >> 8) & 0xff00) | ((x << 8) & 0xff0000) | (x << 24)`)
is silmaril's `byteSwap32`. -/
theorem bswap32Spec_eq (x : BitVec 32) :
    Silmaril.X86.Ladder.LeafArith.bswap32Spec x = Silmaril.X86.Ext.byteSwap32 x := by
  simp only [Silmaril.X86.Ladder.LeafArith.bswap32Spec, Silmaril.X86.Ext.byteSwap32]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

/-- The call-level spec: `rax` is the C result `bswap32_manual((u32) rdi)`, zero-extended. -/
def BswapCallPost (d : SysVCall) (r : Word) : Prop :=
  r = (Silmaril.X86.Ladder.LeafArith.bswap32Spec ((d.regArgs.getD 0 0).setWidth 32)).setWidth 64

/-- **The x86 problem of `bswap32_manual` through the wrapper**: Wasm problem + glue. -/
theorem bswap_xgoal (n : Nat) :
    XGoal bswapProg n (fun d => d.intArgs.length ≤ 6) BswapCallPost :=
  xgoal_of_body (H := Nat) (P := Silmaril.Wasm.Logic.Hoare.detP) (host := fun _ _ _ _ => False)
    bswap_emit n bswap_wasm (preGlue_true _)
    (postGlue_of_frame (Q := fun R v => v = bswap32Val (R .rdi &&& 0xffffffff)) (fun _ _ h => h)
      (fun d σ v hk hv => by
        obtain ⟨h0, -⟩ := entryCore_read d σ hk
        rw [BswapCallPost, hv, h0, ← mov32_val, ← bswap32_val,
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq,
          bswap32Spec_eq]))

theorem bswapBytes_decode : ∀ (k : Nat)
    (_h₁ : k < (bswapProg ++ [(Silmaril.X86.Ext.Instr.ret, 1)]).length) (h₂ : k < bswapBytes.length),
    Silmaril.X86.Ext.decode bswapBytes[k] = some (bswapProg ++ [(Silmaril.X86.Ext.Instr.ret, 1)])[k] ∧
      (bswapProg ++ [(Silmaril.X86.Ext.Instr.ret, 1)])[k].2 = bswapBytes[k].length := by
  decide

/-- **`bswap32_manual` on its bytes, through the System V convention**, for any caller whose
modelled flags are defined and any number of stack arguments. -/
theorem bswap_sysv (d : SysVCall) (hd : d.Valid) (m e : MState) (hs : setup d m = some e)
    (hr : m.memory.Permitted .read (entrySp d.stackArgs.length (m.core.read .rsp)).toNat 8)
    (hb : BytesAt e.memory d.target bswapBytes) (hf : FlagsDef m.core) :
    Silmaril.X86.FnContract.AbiEntry e.core e.memory ∧ ∃ final : MState,
      Silmaril.X86.Ext.Returns SENTINEL e final ∧
      Silmaril.X86.FnContract.AbiReturn e.core e.memory final.core ∧
      BswapCallPost d (final.core.read .rax) :=
  XGoal.of_flags bswap_emit (bswap_xgoal _) d m e hd rfl hd.1 hs hr
    (codeAt_of_bytesAt rfl bswapBytes_decode hb) hf

/-- **The bytes are the ELF's**: the pinned executable loads `89 f8 0f c8 c3` (`bswapBytes`
flattened) at `0x401420` in its `rx` segment. -/
theorem bswap_in_elf :
    Silmaril.X86.Ladder.Pinned.LoadedAt Silmaril.X86.Ladder.Pinned.LeafArith.exe "rx"
      0x401420 bswapBytes.flatten := by
  have h := Silmaril.X86.AbiFunction.LeafArith.loadedAt_slice
    Silmaril.X86.Ladder.Pinned.leafArith_region 0xb0 5 (by decide +kernel)
  have hb : (Silmaril.X86.Ladder.LeafArith.Transcript.region.bytes.drop 0xb0).take 5 =
      bswapBytes.flatten := by decide +kernel
  have ha : Silmaril.X86.Ladder.LeafArith.Transcript.region.base + 0xb0 = 0x401420 := by
    decide +kernel
  rw [hb, ha] at h
  exact h

end Silmaril.Sim.ElfVerify
