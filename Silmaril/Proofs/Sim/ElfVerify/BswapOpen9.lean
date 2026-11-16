module

public import Silmaril.Proofs.Sim.ElfVerify.Bswap
public import Silmaril.Sim.X86.G.Thms
public import Silmaril.X86.Open9.Thms

/-!
# `bswap32_manual`: the ladder's own contract on `Open9.isa`, through the reduction

The ladder states `bswap32_manual`'s contract as `Ladder.LeafArith.bswapSpec` (entry: the whole
transcribed `.text` region loaded at `0x401370`, RIP at `0x401420`; no writes; `rax =
zext (bswap32Spec edi)`) and proves it on `Open.isa` with a BlockCert/Bir block VC
(`bswap32_manual_total`, packaged for `Open9.isa` by `toOpen9`).

**`bswapSpec_total_open9`** proves **the same spec** on `Open9.isa` by the reduction: the
functional part is the Wasm proof `bswap_wasm` (the G code of `Silmaril.Sim.X86.G`, `wpc`), transported by
`Silmaril.Sim.X86.G.xproblem_of_wproblem`; the x86 part is the decoding of the five bytes (cut out of the loaded
region), retirement, the final `ret`, and the `Open → Open9` run bridge.
`bswapContract_same`: the resulting `FnContract Open9.isa` has literally the ladder contract's
spec (`rfl`), so the two proofs are interchangeable.
-/

@[expose] public section

namespace Silmaril.Sim.ElfVerify

open Silmaril.X86 (Reg State MState Word Byte sysv64)
open Silmaril.X86.Ext (Sz RM writeRM retire)
open Silmaril.X86 hiding fetch Fetch
open Silmaril.Sim.X86.G
open Silmaril.X86.Ladder.LeafArith (bswapSpec bswap32Spec r32)

/-- **The x86 problem of the body, solved by reduction to the Wasm problem.** -/
theorem bswap_x86 : XProblem bswapProg (fun _ => True) BswapPost :=
  xproblem_of_wproblem (H := Nat) (P := Silmaril.Wasm.Logic.Hoare.detP) (host := fun _ _ _ _ => False) rfl
    bswap_wasm

/-- The body always retires, memory unchanged. -/
theorem bswapProg_runs (σ : State) (mem : Silmaril.Process.Memory) :
    ∃ σ', runExt bswapProg σ mem = some (σ', mem) := by
  simp [runExt, bswapProg, Silmaril.X86.Ext.exec, writeRM, retire]

/-- The five bytes, cut out of the loaded region. -/
theorem bytesAt_of_loaded {mem : Silmaril.Process.Memory}
    (h : Silmaril.X86.Ext.Loaded mem Ladder.LeafArith.base Ladder.LeafArith.code) :
    BytesAt mem (Ladder.LeafArith.base + BitVec.ofNat 64 0xb0) bswapBytes := by
  have hlen : 0xb5 ≤ Ladder.LeafArith.code.length := by decide +kernel
  have s0 := h.fetchBytes_sub (offset := 0xb0) (len := 2) (by decide) (by omega)
  have s2 := h.fetchBytes_sub (offset := 0xb2) (len := 2) (by decide) (by omega)
  have s4 := h.fetchBytes_sub (offset := 0xb4) (len := 1) (by decide) (by omega)
  have e0 : (Ladder.LeafArith.code.drop 0xb0).take 2 = [0x89, 0xf8] := by decide +kernel
  have e2 : (Ladder.LeafArith.code.drop 0xb2).take 2 = [0x0f, 0xc8] := by decide +kernel
  have e4 : (Ladder.LeafArith.code.drop 0xb4).take 1 = [0xc3] := by decide +kernel
  rw [e0] at s0; rw [e2] at s2; rw [e4] at s4
  refine ⟨?_, ?_, ?_, trivial⟩
  · exact (show (Ladder.LeafArith.base + BitVec.ofNat 64 0xb0).toNat =
      Ladder.LeafArith.base.toNat + 0xb0 by decide) ▸ s0
  · exact (show (Ladder.LeafArith.base + BitVec.ofNat 64 0xb0 + BitVec.ofNat 64 2).toNat =
      Ladder.LeafArith.base.toNat + 0xb2 by decide) ▸ s2
  · exact (show (Ladder.LeafArith.base + BitVec.ofNat 64 0xb0 + BitVec.ofNat 64 2 +
      BitVec.ofNat 64 2).toNat = Ladder.LeafArith.base.toNat + 0xb4 by decide) ▸ s4

/-- **`bswap32_manual` on its bytes** (`Ext` machine): returns to the address on the stack
with `rax = zext (bswap32Spec edi)`, every other register but `rsp` unchanged, memory
unchanged. -/
theorem bswap_returns (m : MState) (exit : Word) (hb : BytesAt m.memory m.core.rip bswapBytes)
    {stack : List Byte} (hs : m.memory.readBytes (m.core.read .rsp).toNat 8 = some stack)
    (hw : Silmaril.X86.wordOfBytes? stack = some exit) :
    ∃ final : MState, Silmaril.X86.Ext.Returns exit m final ∧ final.core.rip = exit ∧
      final.core.read .rax = (bswap32Spec ((m.core.read .rdi).setWidth 32)).setWidth 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rsp → final.core.read r = m.core.read r) ∧
      final.core.read .rsp = m.core.read .rsp + 8#64 ∧ final.memory = m.memory := by
  obtain ⟨σ, mem⟩ := m
  have hcode := codeAt_of_bytesAt (p := bswapProg ++ [(.ret, 1)]) rfl bswapBytes_decode hb
  obtain ⟨hbody, hret, -⟩ := codeAt_append hcode
  obtain ⟨σ', hx⟩ := bswapProg_runs σ mem
  obtain ⟨hbs, hframe⟩ := bswap_x86 σ σ' mem mem trivial hx
  obtain ⟨hrun, hrip⟩ := run_of_runExt (code := bswapCode) rfl exit hbody hx
  rw [← hrip] at hret
  have hrsp : σ'.read .rsp = σ.read .rsp := hframe .rsp (by decide)
  have hpop : Silmaril.X86.popWord σ' mem = some (exit, σ'.write .rsp (σ'.read .rsp + 8#64)) := by
    simp only [Silmaril.X86.popWord, hrsp]
    simp [hs, hw]
  refine ⟨⟨{ σ'.write .rsp (σ'.read .rsp + 8#64) with rip := exit }, mem⟩,
    ⟨2, ⟨σ', mem⟩, hrun, ?_⟩, rfl, ?_, fun r h₁ h₂ => ?_, ?_, rfl⟩
  · simp only [Silmaril.X86.Ext.step, hret, Silmaril.X86.Ext.exec, hpop]
    simp
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rax = _
    rw [State.read_write_other σ' .rsp .rax _ (by decide), hbs, ← mov32_val, ← bswap32_val,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, bswap32Spec_eq]
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read r = _
    rw [State.read_write_other σ' .rsp r _ h₂]
    exact hframe r h₁
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rsp = _
    rw [State.read_write_same, hrsp]

/-- **The ladder's `bswapSpec`, proved on `Open9.isa` through the reduction.** -/
theorem bswapSpec_total_open9 : bswapSpec.Total Open9.isa := by
  intro s _ habi hentry
  obtain ⟨hload, hrip⟩ := hentry
  have hb : BytesAt s.memory s.core.rip bswapBytes := hrip ▸ bytesAt_of_loaded hload
  obtain ⟨final, hret, hfrip, hrax, hframe, hrsp, hmem⟩ :=
    bswap_returns s (Silmaril.X86.FnContract.retOf s.core s.memory) hb habi.returnAddress
      (Silmaril.X86.wordOfBytes?_encodeWords _)
  obtain ⟨hreach, -⟩ := Open.returns_open_ext hret
  refine ⟨final, Open9.reaches_of_open hreach, rfl, ⟨hfrip, hrsp, fun r hr => hframe r ?_ ?_⟩,
    ?_, hrax⟩
  · rintro rfl; simp [sysv64] at hr
  · rintro rfl; exact Silmaril.X86.sysv64_rsp_not_calleeSaved hr
  · show s.memory.WritesWithin final.memory _
    rw [hmem]
    exact Silmaril.Process.Memory.WritesWithin.refl _ _

/-- `bswap32_manual` as a `FnContract Open9.isa`, proved through Wasm. -/
def bswapContract : FnContract Open9.isa := ⟨bswapSpec, bswapSpec_total_open9⟩

/-- **Same statement as the ladder's contract**: the two `FnContract Open9.isa` values have the
same spec; only the proofs differ (Wasm `wpc` + reduction vs. Bir block VC). -/
theorem bswapContract_same :
    bswapContract.toSpec = Ladder.LeafArith.bswap32_manual_contract.toOpen9.toSpec := rfl

end Silmaril.Sim.ElfVerify
