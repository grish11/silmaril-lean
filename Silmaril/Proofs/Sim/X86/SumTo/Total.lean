module

public import Silmaril.Proofs.Sim.X86.SumTo.X86
public import Silmaril.Sim.X86.Loop.Thms
public import Silmaril.X86.Open9.Thms

/-!
# `sum_to`: termination from a Wasm measure, and the `Open9.isa` contract

* `PCM`: the cut-point invariant `PC` of the Wasm solution with a measure (`3·rdi + c`);
  `measured_step`: every dispatcher entry decreases it (a Wasm-level fact, by the same
  straight-line entry lemmas);
* `sum_exists`: hence (`xrun_exists`, with the x86 progress fact that the first `xor`
  defines the modelled flags) an `XRun` exists from every entry state: **termination**;
* **`sumContract : FnContract Open9.isa`** (`sumSpec_total`): `sum_to` in the recommended
  contract form: from every System V entry with the bytes at RIP, a run returns with
  `rax = 0 + 1 + ⋯ + rdi` (mod `2^64`), callee-saved registers and memory unchanged.
-/

@[expose] public section

namespace Silmaril.Sim.X86.SumTo

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word State MState Byte sysv64)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.Loop
open Silmaril.X86

variable {H : Type} {f : Frame}

/-- The cut points of `sum_to` with a measure `k`. -/
def PCM (N b : Word) (k : Nat) (rip rax rdi zf : Word) : Prop :=
  (rip = b ∧ rdi = N ∧ k = 3 * N.toNat + 5) ∨
  (rip = b + 2 ∧ rdi = N ∧ rax = 0 ∧ k = 3 * N.toNat + 4) ∨
  (rip = b + 5 ∧ rdi = N ∧ rax = 0 ∧ zf = b64 (N == 0) ∧ k = 3 * N.toNat + 3) ∨
  (rip = b + 7 ∧ rdi ≠ 0 ∧ rdi.toNat ≤ N.toNat ∧
    rax = BitVec.ofNat 64 (tri N.toNat - tri rdi.toNat) ∧ k = 3 * rdi.toNat + 2) ∨
  (rip = b + 10 ∧ rdi ≠ 0 ∧ rdi.toNat ≤ N.toNat ∧
    rax = BitVec.ofNat 64 (tri N.toNat - tri rdi.toNat) + rdi ∧ k = 3 * rdi.toNat + 1) ∨
  (rip = b + 13 ∧ rdi.toNat < N.toNat ∧ rax = BitVec.ofNat 64 (tri N.toNat - tri rdi.toNat) ∧
    zf = b64 (rdi == 0) ∧ k = 3 * rdi.toNat + 3) ∨
  (rip = b + 15 ∧ rax = BitVec.ofNat 64 (tri N.toNat))

/-- The measured invariant on stores. -/
def JM (f : Frame) (R : Reg → Word) (b : Word) (k : Nat) (s : Store H) : Prop :=
  ∃ rip rax rdi zf, Vals s f R rip rax rdi zf ∧ PCM (R .rdi) b k rip rax rdi zf

/-- The code found at an entry is the code of that entry. -/
private theorem exec_of_lookup {b w : Word} {code code' : List Silmaril.Wasm.Instr} {s s' : Store H}
    (hc : lookupC (compileTab (sumTab b)) w = some code)
    (h' : lookupC (compileTab (sumTab b)) w = some code')
    (he : Silmaril.Wasm.Logic.Core.exec s f [] code' = some (s', f, [])) :
    Silmaril.Wasm.Logic.Core.exec s f [] code = some (s', f, []) := by
  rw [Option.some.inj (hc.symm.trans h')]
  exact he

/-- **Every dispatcher entry decreases the measure** (Wasm level). -/
theorem measured_step (R : Reg → Word) (b : Word) :
    ∀ k (s : Store H), JM f R b k s → ∀ w code, gval s f .rip = some (Val.i64 w) →
      lookupC (compileTab (sumTab b)) w = some code →
      ∃ s', Silmaril.Wasm.Logic.Core.exec s f [] code = some (s', f, []) ∧
        ∃ k' < k, JM f R b k' s' := by
  rintro k s ⟨rip, rax, rdi, zf, hV, hpc⟩ w code hw hc
  have hrw : rip = w := val_i64_inj.mp (Option.some.inj (hV.2.1.symm.trans hw))
  subst hrw
  obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, hk, hle, rfl, rfl⟩ | ⟨rfl, hk, hle, rfl, rfl⟩ | ⟨rfl, hlt, rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      PCM (R .rdi) b k rip rax rdi zf := hpc
  · -- xor %eax, %eax (`b` is named `rip` here)
    obtain ⟨s'', he, hV'⟩ := step0 hV
    exact ⟨s'', exec_of_lookup hc (by simp only [ctab_eq, lookupC, ite_true]) he, _, by omega,
      _, _, _, _, hV', .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
  · -- test %rdi, %rdi
    obtain ⟨s'', he, hV'⟩ := step2 hV
    exact ⟨s'', exec_of_lookup hc (by simp [ctab_eq, lookupC]) he, _, by omega, _, _, _, _, hV',
      .inr (.inr (.inl ⟨by simp [BitVec.add_assoc], rfl, rfl, rfl, rfl⟩))⟩
  · -- je
    show ∃ s', Silmaril.Wasm.Logic.Core.exec s f [] code = some (s', f, []) ∧
      ∃ k' < 3 * (R .rdi).toNat + 3, JM f R b k' s'
    obtain ⟨s'', he, hV'⟩ := step5 hV
    have he' := exec_of_lookup hc (by simp [ctab_eq, lookupC]) he
    cases hN : (R .rdi == 0)
    · exact ⟨s'', he', _, by omega, _, _, _, _, hV', .inr (.inr (.inr (.inl
        ⟨by rw [jcc_bits, hN]; simp [BitVec.add_assoc], by simpa using hN, le_rfl, by simp, rfl⟩)))⟩
    · have h0 : R .rdi = 0 := by simpa using hN
      exact ⟨s'', he', 0, by omega, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inr
        ⟨by rw [jcc_bits, hN]; simp [BitVec.add_assoc], by simp [h0, tri]⟩)))))⟩
  · -- add %rdi, %rax
    obtain ⟨s'', he, zf', hV'⟩ := step7 hV
    exact ⟨s'', exec_of_lookup hc (by simp [ctab_eq, lookupC]) he, _, by omega, _, _, _, _, hV',
      .inr (.inr (.inr (.inr (.inl ⟨by simp [BitVec.add_assoc], hk, hle, rfl, rfl⟩))))⟩
  · -- dec %rdi
    obtain ⟨s'', he, hV'⟩ := step10 hV
    have hk0 : rdi.toNat ≠ 0 := fun e => hk (BitVec.eq_of_toNat_eq (by simpa using e))
    have h1 : (rdi - 1).toNat = rdi.toNat - 1 := by bv_omega
    exact ⟨s'', exec_of_lookup hc (by simp [ctab_eq, lookupC]) he, _, by rw [h1]; omega,
      _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inl
      ⟨by simp [BitVec.add_assoc], by bv_omega, tri_step _ _ hk hle, rfl, rfl⟩)))))⟩
  · -- jne
    show ∃ s', Silmaril.Wasm.Logic.Core.exec s f [] code = some (s', f, []) ∧
      ∃ k' < 3 * rdi.toNat + 3, JM f R b k' s'
    obtain ⟨s'', he, hV'⟩ := step13 hV
    have he' := exec_of_lookup hc (by simp [ctab_eq, lookupC]) he
    cases hN : (rdi == 0)
    · exact ⟨s'', he', _, by omega, _, _, _, _, hV', .inr (.inr (.inr (.inl
        ⟨by rw [b64_xor_one, show (0xfffffffffffffff8 : Word) = 0xfffffffffffffff8 from rfl,
          jcc_bits, hN]; simp [BitVec.add_assoc], by simpa using hN, by omega, rfl, rfl⟩)))⟩
    · have h0 : rdi = 0 := by simpa using hN
      exact ⟨s'', he', 0, by omega, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inr
        ⟨by rw [b64_xor_one, show (0xfffffffffffffff8 : Word) = 0xfffffffffffffff8 from rfl,
          jcc_bits, hN]; simp [BitVec.add_assoc], by simp [h0, tri]⟩)))))⟩
  · -- returned: no entry at `b + 15`
    exact absurd hc (by simp [ctab_eq, lookupC])

theorem lookup_b (b : Word) : lookupI (sumTab b) b = some (.alu .d .xor (.reg .rax) .rax, 2) := by
  simp [sumTab, lookupI]

/-- The x86 progress fact: from RIP `b` (the `xor`, which defines the modelled flags) or with
defined modelled flags, the instruction at RIP retires, and the flags are then defined. -/
theorem sum_progress (b : Word) (m : Silmaril.Process.Memory) :
    ∀ σ i n, (σ.rip = b ∨ Defined σ.flags) → lookupI (sumTab b) σ.rip = some (i, n) →
      ∃ σ₁, Silmaril.X86.Ext.exec i σ m n = .ok σ₁ m ∧ (σ₁.rip = b ∨ Defined σ₁.flags) := by
  intro σ i n hD hl
  have hm := lookupI_mem hl
  obtain ⟨code, hcode⟩ := Option.isSome_iff_exists.mp (supported b _ hm)
  rcases hD with hr | hd
  · rw [hr, lookup_b, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨_, rfl, .inr ⟨rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨σ₁, hx⟩ := emitX_progress hcode hd m
    exact ⟨σ₁, hx, .inr ((emitX_shape hcode hx).2.2 hd)⟩

/-- **Termination**: an `XRun` of `sum_to` exists from every state at its entry. -/
theorem sum_exists (σ : State) (m : Silmaril.Process.Memory) :
    ∃ n σ', XRun (sumTab σ.rip) m n σ σ' := by
  have hE := enc_encStore (H := Nat) σ
  obtain ⟨hl, hr, hri, -, ⟨bz, hz, -⟩, -, -⟩ := hE
  exact xrun_exists (supported σ.rip) (JM encFrame σ.read σ.rip)
    (measured_step σ.read σ.rip) _ (sum_progress σ.rip m) _ (encStore σ) σ
    ⟨σ.rip, σ.read .rax, σ.read .rdi, b64 bz, ⟨hl, hri, hr _, hr _, hz, fun r _ _ => hr r⟩,
      .inl ⟨rfl, rfl, rfl⟩⟩ (enc_encStore σ) (.inl rfl)

/-- The contract's spec. -/
def sumSpec : FnContract.Spec MState where
  entry s := BytesAt s.memory s.core.rip sumBytes
  footprint _ _ := False
  post s t := t.core.read .rax = BitVec.ofNat 64 (tri (s.core.read .rdi).toNat)

/-- **`sum_to` meets its System V contract on `Open9.isa`** (total correctness). -/
theorem sumSpec_total : sumSpec.Total Open9.isa := by
  rintro ⟨σ, mem⟩ _ habi hentry
  simp only [Open9.isa] at habi hentry ⊢
  set exit := Silmaril.X86.FnContract.retOf σ mem
  obtain ⟨htab, hret⟩ := tabAt (codeAt_of_bytesAt rfl sumBytes_decode hentry)
  obtain ⟨n, σe, hx⟩ := sum_exists σ mem
  obtain ⟨hrax, hoth, hrip⟩ := x86_solution σ.rip σ σe mem n rfl hx
  have hrun : Silmaril.Machine.Execution.run (Silmaril.X86.Ext.stepOpt exit) n ⟨σ, mem⟩ =
      some ⟨σe, mem⟩ := run_of_xrun (supported σ.rip) htab exit hx
  have hrsp : σe.read .rsp = σ.read .rsp := hoth .rsp (by decide) (by decide)
  have hstep : Silmaril.X86.Ext.step exit ⟨σe, mem⟩ =
      .returned ⟨{ σe.write .rsp (σe.read .rsp + 8#64) with rip := exit }, mem⟩ := ret_step (exit := exit) (τ := σe) (mem := mem) (by rw [hrip]; exact hret)
    (by rw [hrsp]; exact habi.returnAddress) (Silmaril.X86.wordOfBytes?_encodeWords _)
  have hR : Silmaril.X86.Ext.Returns exit ⟨σ, mem⟩
      ⟨{ σe.write .rsp (σe.read .rsp + 8#64) with rip := exit }, mem⟩ := ⟨n, _, hrun, hstep⟩
  obtain ⟨hreach, -⟩ := Open.returns_open_ext hR
  refine ⟨_, Open9.reaches_of_open hreach, rfl, ⟨rfl, ?_, fun r hr => ?_⟩,
    Silmaril.Process.Memory.WritesWithin.refl _ _, ?_⟩
  · show (σe.write .rsp (σe.read .rsp + 8#64)).read .rsp = _
    rw [State.read_write_same, hrsp]
  · have h1 : r ≠ .rsp := fun e => Silmaril.X86.sysv64_rsp_not_calleeSaved (e ▸ hr)
    have h2 : r ≠ .rax := by rintro rfl; simp [sysv64] at hr
    have h3 : r ≠ .rdi := by rintro rfl; simp [sysv64] at hr
    show (σe.write .rsp (σe.read .rsp + 8#64)).read r = _
    rw [State.read_write_other σe .rsp r _ h1]
    exact hoth r h2 h3
  · show (σe.write .rsp (σe.read .rsp + 8#64)).read .rax = _
    rw [State.read_write_other σe .rsp .rax _ (by decide)]
    exact hrax

/-- **`sum_to` as a System V function contract** on `Open9.isa`. -/
def sumContract : FnContract Open9.isa := ⟨sumSpec, sumSpec_total⟩

end Silmaril.Sim.X86.SumTo
