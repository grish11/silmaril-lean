module

public import Silmaril.Sim.Reduce.Toy.SumTo.Defs
public import Silmaril.Sim.X86.SumTo.Thms
public import Silmaril.Machine.X86.FnContract.Thms
public import Silmaril.Machine.X86.Open9.Thms
public import Silmaril.Sim.Reduce.Loop.Thms

/-!
# The toy's `sum_to`, end to end: proofs

The header is `Silmaril/Sim/Reduce/Toy/SumTo/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.Toy.SumTo

open Silmaril.X86 (Reg Word State)
open Silmaril.X86.Ext
open Silmaril.Sim.X86.Loop Silmaril.Sim.X86.SumTo Silmaril.Sim.Reduce.Loop
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Sim.X86.G

variable {H : Type}


/-- Cut points of `sum_to` with the rank. -/
def RPC (N b rip rdi zf : Word) (k : Nat) : Prop :=
  (rip = b ∧ rdi = N ∧ k = 3 * N.toNat + 5) ∨
  (rip = b + 2 ∧ rdi = N ∧ k = 3 * N.toNat + 4) ∨
  (rip = b + 5 ∧ rdi = N ∧ zf = b64 (N == 0) ∧ k = 3 * N.toNat + 3) ∨
  (rip = b + 7 ∧ rdi ≠ 0 ∧ k = 3 * rdi.toNat + 2) ∨
  (rip = b + 10 ∧ rdi ≠ 0 ∧ k = 3 * rdi.toNat + 1) ∨
  (rip = b + 13 ∧ zf = b64 (rdi == 0) ∧ k = 3 * rdi.toNat + 3) ∨
  (rip = b + 15 ∧ k = 0)

/-- The ranking: a cut point with its rank. -/
def J (b : Word) (f : Frame) (k : Nat) (s : Store H) : Prop :=
  ∃ (N : Word) (R : Reg → Word) (rip rax rdi zf : Word), Vals s f R rip rax rdi zf ∧ RPC N b rip rdi zf k

/-- **The Wasm termination piece, solved**: every dispatcher entry lowers the rank (the
step lemmas `step0`…`step13` evaluate the entries). -/
theorem ranked (b : Word) (f : Frame) : Silmaril.Sim.Reduce.Loop.Ranked (H := H) (compileTab (sumTab b)) f (J b f) := by
  rintro k s w code ⟨N, R, rip, rax, rdi, zf, hV, hpc⟩ hw hlc
  have hwr : w = rip := by
    have := hw.symm.trans hV.2.1; simp only [Option.some.injEq] at this; exact val_i64_inj.mp this
  subst hwr
  rcases hpc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, hrN, rfl, rfl⟩ | ⟨rfl, hk, rfl⟩ |
    ⟨rfl, hk, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [ctab_eq, lookupC, ite_true, Option.some.injEq] at hlc; subst hlc
    obtain ⟨s'', he, hV'⟩ := step0 hV
    exact ⟨s'', _, he, ⟨_, _, _, _, _, _, hV', .inr (.inl ⟨rfl, rfl, rfl⟩)⟩, by omega⟩
  · simp [ctab_eq, lookupC] at hlc; subst hlc
    obtain ⟨s'', he, hV'⟩ := step2 hV
    refine ⟨s'', _, he, ⟨_, _, _, _, _, _, hV', .inr (.inr (.inl ⟨?_, rfl, rfl, rfl⟩))⟩, by omega⟩
    simp [BitVec.add_assoc]
  · simp [ctab_eq, lookupC] at hlc; subst hlc
    subst hrN
    obtain ⟨s'', he, hV'⟩ := step5 hV
    rw [jcc_bits] at hV'
    cases hN : (rdi == 0)
    · refine ⟨s'', _, he, ⟨0, _, _, _, _, _, hV', .inr (.inr (.inr (.inl ⟨?_, by simpa using hN, rfl⟩)))⟩, by omega⟩
      have h0 := hN; simp at h0; simp [h0, BitVec.add_assoc]
    · refine ⟨s'', 0, he, ⟨0, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inr ⟨?_, rfl⟩)))))⟩, by omega⟩
      have h0 := hN; simp at h0; simp [h0, BitVec.add_assoc]
  · simp [ctab_eq, lookupC] at hlc; subst hlc
    obtain ⟨s'', he, zf', hV'⟩ := step7 hV
    refine ⟨s'', _, he, ⟨0, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inl ⟨?_, hk, rfl⟩))))⟩, by omega⟩
    simp [BitVec.add_assoc]
  · simp [ctab_eq, lookupC] at hlc; subst hlc
    obtain ⟨s'', he, hV'⟩ := step10 hV
    refine ⟨s'', _, he, ⟨0, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inl ⟨?_, rfl, rfl⟩)))))⟩, ?_⟩
    · simp [BitVec.add_assoc]
    · have h0 : rdi.toNat ≠ 0 := by simpa [BitVec.toNat_eq] using hk
      rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]; simp; omega
  · simp [ctab_eq, lookupC] at hlc; subst hlc
    obtain ⟨s'', he, hV'⟩ := step13 hV
    rw [b64_xor_one, show (0xfffffffffffffff8 : Word) = 0xfffffffffffffff8 from rfl, jcc_bits] at hV'
    cases hN : (rdi == 0)
    · refine ⟨s'', _, he, ⟨0, _, _, _, _, _, hV', .inr (.inr (.inr (.inl ⟨?_, by simpa using hN, rfl⟩)))⟩, by omega⟩
      have h0 := hN; simp at h0; simp [h0, BitVec.add_assoc]
    · refine ⟨s'', 0, he, ⟨0, _, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inr ⟨?_, rfl⟩)))))⟩, by omega⟩
      have h0 := hN; simp at h0; simp [h0, BitVec.add_assoc]
  · simp [ctab_eq, lookupC] at hlc


theorem triN_eq : ∀ n, Silmaril.Sim.Reduce.Toy.triN n = Silmaril.Sim.X86.SumTo.tri n
  | 0 => rfl
  | n + 1 => by simp [Silmaril.Sim.Reduce.Toy.triN, Silmaril.Sim.X86.SumTo.tri, triN_eq n]

open Silmaril.Machine.X86 Silmaril.Sim.X86.G in
/-- **The ISA goal from the pieces**: the x86 problem (functional post) and termination/frame,
through the bytes (`decide`), the final `ret`, and the open machine. -/
theorem isa_of (hx86 : X86Stmt) (hterm : TermStmt) : Silmaril.Sim.Reduce.Toy.isaGoal .sumTo := by
  intro base
  refine FnContract.Spec.Total.toOpen9 (FnContract.total_of_ext_returns _ fun m ha he => ?_)
  obtain ⟨hload, hrip⟩ := he
  obtain ⟨σ, mem⟩ := m
  simp only at hload hrip ha ⊢
  have hb : BytesAt mem σ.rip sumBytes := by
    rw [hrip]; exact bytesAt_of_loaded hload sumBytes 0 (by decide) (by decide) (by decide)
  obtain ⟨htab, hret⟩ := tabAt (codeAt_of_bytesAt rfl sumBytes_decode hb)
  obtain ⟨k, σ', hrun, hfr⟩ := hterm σ.rip mem σ rfl
  obtain ⟨hrax, hfr', hrip'⟩ := hx86 σ.rip σ σ' mem k rfl hrun
  have hrsp : σ'.read .rsp = σ.read .rsp := hfr' .rsp (by decide) (by decide)
  have hstep : Silmaril.X86.Ext.step (Open.retOf σ mem) ⟨σ', mem⟩ =
      .returned ⟨{ σ'.write .rsp (σ'.read .rsp + 8#64) with rip := Open.retOf σ mem }, mem⟩ := ret_step (exit := Open.retOf σ mem) (τ := σ') (by rw [hrip']; exact hret)
    (by rw [hrsp]; exact ha.returnAddress) (Silmaril.X86.wordOfBytes?_encodeWords _)
  refine ⟨_, ⟨k, ⟨σ', mem⟩, Silmaril.Sim.Reduce.Loop.run_of_xrun (supported σ.rip) htab _ hrun, hstep⟩, ?_, ?_, ?_, ?_⟩
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rsp = _
    rw [State.read_write_same, hrsp]
  · intro r hr
    have h₁ : r ≠ .rax := by simp [Silmaril.X86.sysv64] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h₂ : r ≠ .rdi := by simp [Silmaril.X86.sysv64] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h₃ : r ≠ .rsp := by simp [Silmaril.X86.sysv64] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    show (σ'.write .rsp (σ'.read .rsp + 8#64)).read r = _
    rw [State.read_write_other σ' .rsp r _ h₃, hfr r h₁ h₂]
  · exact Silmaril.Process.Memory.WritesWithin.refl _ _
  · show (σ'.write .rsp (σ'.read .rsp + 8#64)).read .rax = Silmaril.Sim.Reduce.Toy.tri (σ.read .rdi)
    rw [State.read_write_other σ' .rsp .rax _ (by decide), hrax]
    simp [Silmaril.Sim.Reduce.Toy.tri, triN_eq]


/-- The x86 problem, from the Wasm piece (`xlproblem_of_lproblem`). -/
theorem x86_of_piece (h : PieceStmt) : X86Stmt := fun b =>
  xlproblem_of_lproblem (H := Nat) (P := Silmaril.Wasm.Logic.Hoare.detP) (host := fun _ _ _ _ => False)
    (supported b) (h b (H := Nat) _ _)

/-- The Wasm piece, solved (`wasm_solution`, dispatcher cut-point rule). -/
theorem piece : PieceStmt := fun b _ _ _ => wasm_solution b

theorem sumTab_place (b : Word) : sumTab b = place b sumRel := by
  simp [place, sumRel, sumTab]

/-- The flag dataflow check of `sum_to`, by evaluation. -/
theorem sum_flagsOK : flagsOK sumRel sumAnn 0 = true := by decide

/-- The Wasm termination piece holds. -/
theorem rank : RankStmt := by
  intro b H f
  refine ⟨J b f, ranked b f, fun s R hG hw => ?_⟩
  obtain ⟨hl, hr, -, -, ⟨bz, hz⟩, -, -⟩ := hG
  exact ⟨3 * (R .rdi).toNat + 5, R .rdi, R, b, R .rax, R .rdi, b64 bz,
    ⟨hl, hw, hr _, hr _, hz, fun r _ _ => hr r⟩, .inl ⟨rfl, rfl, rfl⟩⟩

/-- **Termination and frame from the Wasm ranking** (generic `xrun_of_ranked`, on the canonical
store encoding the entry state). -/
theorem term_of_rank (h : RankStmt) : TermStmt := by
  intro b m σ hrip
  obtain ⟨J, hR, hent⟩ := h b (H := Nat) encFrame
  have hE := enc_encStore (H := Nat) σ
  obtain ⟨k, hJ⟩ := hent _ σ.read hE.gregs (by rw [← hrip]; exact hE.2.2.1)
  rw [sumTab_place] at hR ⊢
  obtain ⟨j, σ', hrun, hfr⟩ := xrun_of_ranked (sumTab_place b ▸ supported b) sum_flagsOK hR m k _ σ
    hJ hE (flagInv_entry sum_flagsOK (by rw [hrip]; simp))
  refine ⟨j, σ', hrun, fun r h₁ h₂ => hfr r ?_⟩
  simp [tabWrites, place, sumRel, writesOf, h₁, h₂]

/-- Termination and frame, solved (through the Wasm ranking). -/
theorem term : TermStmt := term_of_rank rank

/-- **The toy ISA goal for `sum_to`, solved** from Wasm pieces (functional: the dispatcher's
partial-correctness piece; termination and frame: the ranking piece) and generic theorems. -/
theorem isa_sumTo : Silmaril.Sim.Reduce.Toy.isaGoal .sumTo := isa_of (x86_of_piece piece) term

end Silmaril.Sim.Reduce.Toy.SumTo
