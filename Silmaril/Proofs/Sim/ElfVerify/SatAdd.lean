module

public import Silmaril.Proofs.Sim.ElfVerify.SatAddWasm
public import Silmaril.X86.Ladder.LeafArith.Thms
public import Silmaril.X86.Open9.Thms

/-!
# `sat_add_u32`: the ladder's own contract on `Open9.isa`, through the reduction

* `x86_solution`: the x86 problem of the table (`XLProblem`), by `Silmaril.Sim.X86.Loop.xlproblem_of_lproblem` from
  the Wasm solution `wasm_solution` (partial correctness, every table run);
* `sat_exists`: **termination**, from the Wasm ranking `ranked` by the generic
  `xrun_of_ranked` and the decidable flag dataflow check `sat_flagsOK`;
* **`satSpec_total_open9`**: the ladder's `Ladder.LeafArith.satSpec` (whole region loaded at
  `0x401370`, RIP at `0x401400`, no writes, `rax = zext (satAddSpec edi esi)`) on `Open9.isa`;
  `satContract_same`: the same spec as the ladder's `sat_add_u32_contract.toOpen9` (`rfl`).

The x86-specific reasoning: the 29 bytes (cut out of the loaded region) decode to the table and
two `ret`s (`decide`), the last step is a `ret`, and the `Open → Open9` bridge. The control
flow (both paths, the backward `jmp`), the values and the frame come from Wasm.
-/

@[expose] public section

namespace Silmaril.Sim.ElfVerify.SatAdd

open Silmaril.X86 (Reg State MState Word Byte sysv64)
open Silmaril.X86.Ext (fetch)
open Silmaril.X86 hiding fetch Fetch
open Silmaril.Sim.X86.G Silmaril.Sim.X86.Loop Silmaril.Sim.Reduce.Loop

theorem supported (b : Word) : Supported (satTab b) := by
  intro e he
  simp only [satTab, place, satRel, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **The x86 problem of the table, solved by reduction to the Wasm problem.** -/
theorem x86_solution (b : Word) : XLProblem (satTab b) (fun _ w => w = b) SatPost :=
  xlproblem_of_lproblem (H := Nat) (P := Silmaril.Wasm.Logic.Hoare.detP) (host := fun _ _ _ _ => False)
    (supported b) (wasm_solution b)

/-- Offsets where the modelled flags are defined (everything after the `xor`). -/
def satAnn : List Nat := [2, 4, 6, 8, 0xa, 0x10, 0x16, 0x1b]

/-- The flag dataflow check, by evaluation. -/
theorem sat_flagsOK : flagsOK satRel satAnn 0 = true := by decide

/-- **Termination and frame** from the Wasm ranking. -/
theorem sat_exists (σ : State) (m : Silmaril.Process.Memory) :
    ∃ n σ', XRun (satTab σ.rip) m n σ σ' ∧
      ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rdi → σ'.read r = σ.read r := by
  have hE := enc_encStore (H := Nat) σ
  obtain ⟨hl, hr, hri, ⟨bc, hc, -⟩, ⟨bz, hz, -⟩, -, -⟩ := hE
  have hJ : JM encFrame σ.read σ.rip 12 (encStore σ) :=
    ⟨σ.rip, σ.read .rax, σ.read .rdx, σ.read .rdi, b64 bc, b64 bz,
      ⟨hl, hri, hr _, hr _, hr _, hc, hz, fun r _ _ _ => hr r⟩, .inl ⟨rfl, rfl, rfl⟩⟩
  obtain ⟨j, σ', hrun, hfr⟩ := xrun_of_ranked (supported σ.rip) sat_flagsOK
    (ranked σ.read σ.rip) m 12 _ σ hJ (enc_encStore σ)
    (flagInv_entry sat_flagsOK (by simp))
  refine ⟨j, σ', hrun, fun r h₁ h₂ h₃ => hfr r ?_⟩
  simp [tabWrites, place, satRel, writesOf, h₁, h₂, h₃]

/-- The bytes at offset `0x90` of the region: the body with its padding and both `ret`s. -/
def satBytes : List (List Byte) :=
  [[0x31, 0xd2], [0x01, 0xf7], [0x72, 0x10], [0x89, 0xf8], [0x85, 0xd2], [0x75, 0x04], [0xc3],
   [0x0f, 0x1f, 0x00], [0xb8, 0xff, 0xff, 0xff, 0xff], [0xc3], [0xba, 0x01, 0x00, 0x00, 0x00],
   [0xeb, 0xe9]]

/-- Their decoding, in address order. -/
def satProg : XProg :=
  [(.alu .d .xor (.reg .rdx) .rdx, 2), (.alu .d .add (.reg .rdi) .rsi, 2), (.jcc8 .b 0x10, 2),
   (.mov .d (.reg .rax) .rdi, 2), (.test .d (.reg .rdx) .rdx, 2), (.jcc8 .ne 4, 2), (.ret, 1),
   (.nop 2, 3), (.movI32 .rax 0xffffffff, 5), (.ret, 1), (.movI32 .rdx 1, 5), (.jmp8 0xe9, 2)]

theorem satBytes_decode : ∀ (k : Nat) (_h₁ : k < satProg.length) (h₂ : k < satBytes.length),
    Silmaril.X86.Ext.decode satBytes[k] = some satProg[k] ∧ satProg[k].2 = satBytes[k].length := by
  decide +kernel

set_option maxHeartbeats 2000000 in
theorem tabAt {mem : Silmaril.Process.Memory} {b : Word} (h : CodeAt mem b satProg) :
    TabAt mem (satTab b) ∧ fetch mem (b + 0xc).toNat = .decoded .ret 1 ∧
      fetch mem (b + 0x15).toNat = .decoded .ret 1 := by
  simp only [satProg, CodeAt, BitVec.add_assoc, BitVec.reduceAdd] at h
  obtain ⟨h0, h2, h4, h6, h8, ha, hc, -, h10, h15, h16, h1b, -⟩ := h
  refine ⟨?_, hc, h15⟩
  intro e he
  simp only [satTab, place, satRel, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using h0
  · exact h2
  · exact h4
  · exact h6
  · exact h8
  · exact ha
  · exact h10
  · exact h16
  · exact h1b

theorem ret_step {exit : Word} {τ : State} {mem : Silmaril.Process.Memory} {stack : List Byte}
    (hf : fetch mem τ.rip.toNat = .decoded .ret 1)
    (hs : mem.readBytes (τ.read .rsp).toNat 8 = some stack)
    (hw : Silmaril.X86.wordOfBytes? stack = some exit) :
    Silmaril.X86.Ext.step exit ⟨τ, mem⟩ =
      .returned ⟨{ τ.write .rsp (τ.read .rsp + 8#64) with rip := exit }, mem⟩ := by
  simp [Silmaril.X86.Ext.step, hf, Silmaril.X86.Ext.exec, Silmaril.X86.popWord, hs, hw]

theorem satAdd_eq (a b : BitVec 32) : satAdd a b = Ladder.LeafArith.satAddSpec a b := rfl

private theorem ne_of_calleeSaved {r x : Reg} (hx : x ∉ sysv64.calleeSaved)
    (hr : r ∈ sysv64.calleeSaved) : r ≠ x := fun e => hx (e ▸ hr)

/-- **The ladder's `satSpec`, proved on `Open9.isa` through the reduction.** -/
theorem satSpec_total_open9 : Ladder.LeafArith.satSpec.Total Open9.isa := by
  rintro ⟨σ, mem⟩ _ habi0 ⟨hload0, hrip0⟩
  have habi : FnContract.AbiEntry σ mem := habi0
  have hload : Silmaril.X86.Ext.Loaded mem Ladder.LeafArith.base Ladder.LeafArith.code := hload0
  have hrip : σ.rip = Ladder.LeafArith.base + 144#64 := hrip0
  simp only [Open9.isa]
  set exit := Silmaril.X86.FnContract.retOf σ mem
  have hb : BytesAt mem σ.rip satBytes := by
    rw [hrip]
    exact bytesAt_of_loaded hload satBytes 0x90 (by decide) (by decide +kernel) (by decide +kernel)
  obtain ⟨htab, hret1, hret2⟩ := tabAt (codeAt_of_bytesAt rfl satBytes_decode hb)
  obtain ⟨n, σe, hx, -⟩ := sat_exists σ mem
  obtain ⟨hrax, hoth, hexit⟩ := x86_solution σ.rip σ σe mem n rfl hx
  have hrsp : σe.read .rsp = σ.read .rsp := hoth .rsp (by decide) (by decide) (by decide)
  have hret : fetch mem σe.rip.toNat = .decoded .ret 1 := by
    rcases hexit with h | h
    · rw [h]; exact hret1
    · rw [h]; exact hret2
  have hR : Silmaril.X86.Ext.Returns exit ⟨σ, mem⟩
      ⟨{ σe.write .rsp (σe.read .rsp + 8#64) with rip := exit }, mem⟩ :=
    ⟨n, _, Silmaril.Sim.Reduce.Loop.run_of_xrun (supported σ.rip) htab exit hx,
      ret_step (exit := exit) (τ := σe) (mem := mem) hret
        (by rw [hrsp]; exact habi.returnAddress) (Silmaril.X86.wordOfBytes?_encodeWords _)⟩
  obtain ⟨hreach, -⟩ := Open.returns_open_ext hR
  refine ⟨_, Open9.reaches_of_open hreach, rfl, ⟨rfl, ?_, fun r hr => ?_⟩,
    Silmaril.Process.Memory.WritesWithin.refl _ _, ?_⟩
  · show (σe.write .rsp (σe.read .rsp + 8#64)).read .rsp = _
    rw [State.read_write_same, hrsp]
  · have h1 : r ≠ .rsp := fun e => Silmaril.X86.sysv64_rsp_not_calleeSaved (e ▸ hr)
    show (σe.write .rsp (σe.read .rsp + 8#64)).read r = _
    rw [State.read_write_other σe .rsp r _ h1]
    exact hoth r (ne_of_calleeSaved (by simp [sysv64]) hr) (ne_of_calleeSaved (by simp [sysv64]) hr)
      (ne_of_calleeSaved (by simp [sysv64]) hr)
  · show (σe.write .rsp (σe.read .rsp + 8#64)).read .rax = _
    rw [State.read_write_other σe .rsp .rax _ (by decide)]
    exact hrax

/-- `sat_add_u32` as a `FnContract Open9.isa`, proved through Wasm. -/
def satContract : FnContract Open9.isa := ⟨Ladder.LeafArith.satSpec, satSpec_total_open9⟩

/-- **Same statement as the ladder's contract** (only the proofs differ). -/
theorem satContract_same :
    satContract.toSpec = Ladder.LeafArith.sat_add_u32_contract.toOpen9.toSpec := rfl

end Silmaril.Sim.ElfVerify.SatAdd
