module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitInv

/-! # GNU `sha256sum` witness: the library's callback entries keep the resource invariant

The library enters `main` and the exit callbacks on the fresh stack `stk2R` (`rspT`), with the
gate word on top:

* `callMem m`: the memory `m` with the stack added (exit callbacks: every stream is kept);
* `mainMem m`: the same with everything below the library's `lo` unmapped (a `main` entry
  that the start-up could not have produced: no heap block and no stream, so the resource
  invariant `InvR` holds whatever came before).

`enters_call`, `enters_main`: these are callback entries (`Enters`). `invR_entM`,
`invR_mainMem`: the main entries satisfy `InvR`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.Ext (loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total

/-- The resource part of the invariant (what the library promises at `main`'s entry). -/
def InvR (s : PState) : Prop := InMain s.g → InvZ s ∧ InvS s

/-- The library's `lo` for the slot representation. -/
def loA : Nat := A0 + K0 * S0

theorem loA_eq : loA = 0x11000000 := rfl

def callMem (m : Memory) : Memory := ⟨m.regions ++ [stk2R], Memory.install m.bytes rspT.toNat gateBytes⟩

def mainMem (m : Memory) : Memory :=
  ⟨m.regions.flatMap (cutR 0 loA) ++ [stk2R], Memory.install m.bytes rspT.toNat gateBytes⟩

/-- A callback's registers on the fresh stack. -/
def coreE (f a1 a2 a3 fsb : Word) : State :=
  ⟨fun r => if r = .rsp then rspT else if r = .rdi then a1 else if r = .rsi then a2 else if r = .rdx then a3
    else 0, f, ⟨none, none, none, none, none, none⟩, fsb⟩

section
variable (f a1 a2 a3 fsb : Word)
theorem coreE_rsp : (coreE f a1 a2 a3 fsb).read .rsp = rspT := by simp [coreE, State.read]
theorem coreE_rdi : (coreE f a1 a2 a3 fsb).read .rdi = a1 := by simp [coreE, State.read]
theorem coreE_rsi : (coreE f a1 a2 a3 fsb).read .rsi = a2 := by simp [coreE, State.read]
theorem coreE_rdx : (coreE f a1 a2 a3 fsb).read .rdx = a3 := by simp [coreE, State.read]
end

def InStk2 (a : Nat) : Prop := stk2Lo ≤ a ∧ a < stk2Lo + 0x2000

theorem stk2_contains {a : Nat} : stk2R.Contains a ↔ InStk2 a := Iff.rfl

theorem permits_app_stk2 (rs : List Region) (b : Silmaril.Process.ByteMemory) (acc : Access) (a : Nat)
    (h : ¬ InStk2 a) : (Memory.mk (rs ++ [stk2R]) b).permits acc a = (Memory.mk rs b).permits acc a := by
  unfold Memory.permits
  simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  have : decide (stk2R.Contains a) = false := by simpa [stk2_contains] using h
  rw [this]; simp

theorem permits_stk2 (rs : List Region) (b : Silmaril.Process.ByteMemory) {acc : Access}
    (hacc : acc = .read ∨ acc = .write) {a : Nat} (h : InStk2 a) :
    (Memory.mk (rs ++ [stk2R]) b).permits acc a = true :=
  permits_of_mem (base := stk2Lo) (size := 0x2000) (p := perm true true false) (by simp [stk2R]) h.1 h.2
    (by rcases hacc with rfl | rfl <;> rfl)

theorem install_gate_out (b : Silmaril.Process.ByteMemory) {a : Nat} (h : ¬ InStk2 a) :
    (Memory.install b rspT.toNat gateBytes).get? a = b.get? a :=
  Memory.install_outside _ _ _ _ (by rw [gateBytes_length, rspT_toNat]; simp only [InStk2, stk2Lo] at h; omega)

theorem callMem_keep (m : Memory) : Keeps (fun a => ¬ InStk2 a) m (callMem m) := fun a ha =>
  ⟨install_gate_out _ ha, fun acc => permits_app_stk2 _ _ acc a ha⟩

theorem mainMem_keep (m : Memory) : Keeps (fun a => ¬ InStk2 a ∧ loA ≤ a) m (mainMem m) := fun a ha =>
  ⟨install_gate_out _ ha.1, fun acc => by
    unfold mainMem
    rw [permits_app_stk2 _ _ acc a ha.1]
    unfold Memory.permits
    exact any_cut 0 loA acc a (Or.inr ha.2) _⟩

theorem mainMem_low (m : Memory) {a : Nat} (h : a < loA) (acc : Access) : (mainMem m).permits acc a = false := by
  have hs : ¬ InStk2 a := by simp only [InStk2, stk2Lo]; rw [loA_eq] at h; omega
  unfold mainMem
  rw [permits_app_stk2 _ _ acc a hs]
  unfold Memory.permits
  exact any_cut_in 0 loA acc a (Nat.zero_le _) h _

theorem kept_hi {a : Nat} (h : Wf.Kept a) : loA ≤ a ∧ ¬ InStk2 a := by
  rw [kept_iff] at h
  simp only [loA_eq, InStk2, stk2Lo]
  omega

theorem gate_read (rs : List Region) (b : Silmaril.Process.ByteMemory) :
    (Memory.mk (rs ++ [stk2R]) (Memory.install b rspT.toNat gateBytes)).readBytes rspT.toNat 8 =
      some gateBytes := by
  have hn : rspT.toNat + gateBytes.length < 2 ^ 64 := by rw [gateBytes_length, rspT_toNat]; omega
  rw [← gateBytes_length]
  refine read_of hn (fun k hk => ?_) (fun k hk => Memory.install_get _ _ _ _ hk)
  rw [gateBytes_length] at hk
  exact permits_stk2 _ _ (Or.inl rfl) (by simp only [InStk2, stk2Lo]; rw [rspT_toNat]; omega)

theorem stackRoom_stk2 (rs : List Region) (b : Silmaril.Process.ByteMemory) (W : World)
    (hW : ∀ a, W.Kept a → Wf.Kept a) : StackRoom W (Memory.mk (rs ++ [stk2R]) b) rspT := by
  refine ⟨by rw [rspT_toNat]; omega, by rw [rspT_toNat]; omega, fun a h1 h2 => ?_⟩
  rw [rspT_toNat] at h1 h2
  have hs : InStk2 a := by simp only [InStk2, stk2Lo]; omega
  refine ⟨permits_stk2 _ _ (Or.inl rfl) hs, permits_stk2 _ _ (Or.inr rfl) hs, fun hk => ?_⟩
  exact (kept_hi (hW a hk)).2 hs

/-- **Entering a callback from `u` on the fresh stack**, the memory `m` keeping `u`'s kept bytes. -/
theorem enters_of {W : World} (hW : ∀ a, W.Kept a ↔ Wf.Kept a) (hg : W.gate = gate0) (u : PState)
    (f a1 a2 a3 : Word) (G : Ghost) (rs : List Region) (b : Silmaril.Process.ByteMemory)
    (hk : Keeps W.Kept u.m.memory (Memory.mk (rs ++ [stk2R]) (Memory.install b rspT.toNat gateBytes))) :
    Enters W u ⟨⟨coreE f a1 a2 a3 u.m.core.fsBase, Memory.mk (rs ++ [stk2R]) (Memory.install b rspT.toNat gateBytes)⟩, G⟩
      f := by
  refine ⟨rfl, by rw [coreE_rsp, rspT_toNat], ?_, ?_, hk, rfl⟩
  · show Memory.readBytes _ ((coreE f a1 a2 a3 u.m.core.fsBase).read .rsp).toNat 8 = _
    rw [coreE_rsp, gate_read, hg]; rfl
  · rw [coreE_rsp]; exact stackRoom_stk2 rs _ W fun a h => (hW a).1 h

theorem callMem_kept {W : World} (hW : ∀ a, W.Kept a ↔ Wf.Kept a) (m : Memory) : Keeps W.Kept m (callMem m) :=
  (callMem_keep m).mono fun a h => (kept_hi ((hW a).1 h)).2

theorem mainMem_kept {W : World} (hW : ∀ a, W.Kept a ↔ Wf.Kept a) (m : Memory) : Keeps W.Kept m (mainMem m) :=
  (mainMem_keep m).mono fun a h => ⟨(kept_hi ((hW a).1 h)).2, (kept_hi ((hW a).1 h)).1⟩

/-! ## The resource invariant at the main entries -/

theorem invR_mainMem (u : PState) (c : State) (G : Ghost) : InvR ⟨⟨c, mainMem u.m.memory⟩, G⟩ := by
  intro _
  refine ⟨⟨[], by simp, by simp, fun x hx hr => ?_⟩, ⟨[], by simp, fun f st hf => ?_⟩⟩
  · have := mainMem_low u.m.memory (show x < loA by rw [loA_eq]; unfold A0 at hx; omega) .read
    rw [this] at hr; cases hr
  · exfalso
    obtain ⟨-, -, hp⟩ := perm_of_read hf.2.2.1
    have hsl := slot_lt hf.1
    have := mainMem_low u.m.memory (show f.toNat + 0 < loA by rw [loA_eq]; unfold A0 K0 S0 at hsl; omega) .read
    rw [hp 0 (by omega)] at this; cases this

theorem memM_low {args : List (List Byte)} (data : List Byte) {x : Nat} (hx : x < A0) : (memMA args data).permits .read x = false := by
  unfold Memory.permits
  rw [List.any_eq_false]
  intro r hr hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hc1, hc2⟩, -⟩ := hc
  have e1 : stackLo = 0x7ffffffdd000 := by unfold stackLo; rw [sp0_toNat]
  have e2 : libLo = 0x7ffff7e04000 := by unfold libLo; rw [lb0_toNat]
  unfold A0 at hx
  simp only [memMA, regions0, exeRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl) | rfl | rfl
  all_goals first
    | (simp only [b0_toNat, e1, e2, fs0_toNat] at hc1 hc2; omega)
    | (simp only [stk2R, stk2Lo] at hc1 hc2; omega)
    | (simp only [arenaR, A0] at hc1 hc2; omega)

theorem memM_slot_nr {args : List (List Byte)} (data : List Byte) {a : Nat} (h1 : A0 + 3 * S0 ≤ a) (h2 : a < loA) :
    (memMA args data).permits .read a = false := by
  unfold Memory.permits
  rw [List.any_eq_false]
  intro r hr hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hc1, hc2⟩, -⟩ := hc
  have e1 : stackLo = 0x7ffffffdd000 := by unfold stackLo; rw [sp0_toNat]
  have e2 : libLo = 0x7ffff7e04000 := by unfold libLo; rw [lb0_toNat]
  rw [loA_eq] at h2
  unfold A0 S0 at h1
  simp only [memMA, regions0, exeRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl) | rfl | rfl
  all_goals first
    | (simp only [b0_toNat, e1, e2, fs0_toNat] at hc1 hc2; omega)
    | (simp only [stk2R, stk2Lo] at hc1 hc2; omega)
    | (simp only [arenaR, A0, S0] at hc1 hc2; omega)

theorem invR_entM (data : List Byte) (f a3 : Word) (g : Ghost) : InvR (entM data f a3 g) := by
  intro _
  refine ⟨⟨[], by simp, by simp, fun x hx hr => ?_⟩, ⟨[0, 1, 2], by simp, fun f' st hf => ?_⟩⟩
  · have := memM_low (args := [a00]) data hx
    change (memM data).permits .read x = true at hr
    rw [this] at hr; cases hr
  · obtain ⟨k, hk, he⟩ := hf.1
    obtain ⟨-, -, hp⟩ := perm_of_read hf.2.2.1
    have hk3 : k < 3 := by
      by_contra hc
      have hp0 := hp 0 (by omega)
      change (memM data).permits .read (f'.toNat + 0) = true at hp0
      have hKS : k < 15 := hk
      have := memM_slot_nr (args := [a00]) data (a := f'.toNat + 0) (by rw [he]; unfold A0 S0; omega)
        (by rw [he, loA_eq]; unfold A0 S0; omega)
      rw [hp0] at this; cases this
    refine ⟨k, by simp; omega, hk, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [he, slotW_toNat (by unfold K0; omega)]

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
