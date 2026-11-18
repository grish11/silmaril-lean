module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitTasks

/-! # GNU `sha256sum` witness: `main` entered with the library's guarantee (`Task.mainLibReach`)

From every gate state `u` with the kernel's kept memory and `fsBase`, the library can enter
`main` with `MainLib`: the entry state `entM` has a fixed memory `memM data` (the kernel's
memory `memW (stkOf [a00])` plus the three streams in the first slots of the arena and a fresh
stack below the kernel's stack page whose top word is the gate), `argc = 1`, `argv = sp0 + 8`.
Since `memM data` agrees with the kernel's memory on the kept addresses, and `u` keeps them
from the kernel's state, `Enters` holds (`mainLib_reach`).

The stream slots hold the whole unread input, so standard input must fit a slot:
`64 + data.length ≤ S0` (1 MiB).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.Ext (loadN leBytes leValue)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Proc.Witness
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total

/-! ## The memory at `main`'s entry -/

/-- `main`'s stack pointer: `sp0 - 0x1008` (16-byte aligned plus 8). -/
def rspT : Word := 0x7ffffffdcff8#64
/-- A fresh stack below the kernel's stack page. -/
def stk2Lo : Nat := 0x7ffffffdb000
def arenaR : Region := ⟨A0, 3 * S0, perm true false false⟩
def stk2R : Region := ⟨stk2Lo, 0x2000, perm true true false⟩
def gateBytes : List Byte := Silmaril.Machine.LittleEndian.encodeWords [gate0]

theorem rspT_toNat : rspT.toNat = 0x7ffffffdcff8 := rfl
theorem gateBytes_length : gateBytes.length = 8 := by simp [gateBytes]

def mem0A (args : List (List Byte)) : Memory := memW (stkOf args)
abbrev mem0 : Memory := mem0A [a00]

def bytesMA (args : List (List Byte)) (data : List Byte) : Silmaril.Process.ByteMemory :=
  Memory.install (Memory.install (Memory.install (Memory.install (mem0A args).bytes A0 (enc (outSt 1)))
    (A0 + S0) (enc (outSt 2))) (A0 + 2 * S0) (enc (stdinSt data))) rspT.toNat gateBytes

/-- **The memory at `main`'s entry.** -/
def memMA (args : List (List Byte)) (data : List Byte) : Memory := ⟨regions0 ++ [arenaR, stk2R], bytesMA args data⟩
abbrev bytesM (data : List Byte) : Silmaril.Process.ByteMemory := bytesMA [a00] data
abbrev memM (data : List Byte) : Memory := memMA [a00] data

/-- The addresses `memM` adds. -/
def New (a : Nat) : Prop := (A0 ≤ a ∧ a < A0 + 3 * S0) ∨ (stk2Lo ≤ a ∧ a < stk2Lo + 0x2000)

theorem enc_out_length (fd : Nat) : (enc (outSt fd)).length = 64 := by
  rw [enc_length]; rfl

theorem permits_memM {args : List (List Byte)} (data : List Byte) (acc : Access) (a : Nat) (h : ¬ New a) :
    (memMA args data).permits acc a = (mem0A args).permits acc a := by
  simp only [New, A0, S0] at h
  simp only [Memory.permits, memMA, mem0A, memW, List.any_append, List.any_cons, List.any_nil,
    arenaR, stk2R, Silmaril.Process.Region.Contains, A0, S0, stk2Lo]
  have h1 : ¬ (0x10000000 ≤ a ∧ a < 0x10000000 + 3 * 0x100000) := fun hh => h (Or.inl hh)
  have h2 : ¬ (0x7ffffffdb000 ≤ a ∧ a < 0x7ffffffdb000 + 0x2000) := fun hh => h (Or.inr hh)
  simp [h1, h2]

theorem keepsNew {args : List (List Byte)} (data : List Byte) (hd : 64 + data.length ≤ S0) :
    Keeps (fun a => ¬ New a) (mem0A args) (memMA args data) := by
  intro a ha
  refine ⟨?_, fun acc => permits_memM data acc a ha⟩
  have hl := enc_length (stdinSt data)
  have hs : (stdinSt data).rd = data := rfl
  rw [hs] at hl
  simp only [New, A0, S0, stk2Lo] at ha hd
  show (bytesMA args data).get? a = _
  unfold bytesMA
  rw [Memory.install_outside _ _ _ _ (by rw [gateBytes_length, rspT_toNat]; omega),
    Memory.install_outside _ _ _ _ (by rw [hl]; simp only [A0, S0]; omega),
    Memory.install_outside _ _ _ _ (by rw [enc_out_length]; simp only [A0, S0]; omega),
    Memory.install_outside _ _ _ _ (by rw [enc_out_length]; simp only [A0]; omega)]

theorem Keeps.symm' {P : Nat → Prop} {m m' : Memory} (h : Keeps P m m') : Keeps P m' m :=
  fun a ha => ⟨(h a ha).1.symm, fun acc => ((h a ha).2 acc).symm⟩

theorem kept_not_new {a : Nat} (h : Wf.Kept a) : ¬ New a := by
  have h' : ShaImg b0 a ∨ args0 a ∨ tls0 a := h
  simp only [ShaImg, args0, tls0, b0_toNat, sp0_toNat, fs0_toNat, lb0_toNat] at h'
  simp only [New, A0, S0, stk2Lo]
  omega

/-! ## Reading the memory -/

theorem permits_of_mem {m : Memory} {base size : Nat} {p : Permissions} {acc : Access} {a : Nat}
    (hr : (⟨base, size, p⟩ : Region) ∈ m.regions)
    (h1 : base ≤ a) (h2 : a < base + size) (hp : p.allows acc = true) :
    m.permits acc a = true := by
  unfold Memory.permits
  rw [List.any_eq_true]
  exact ⟨_, hr, by simp [Silmaril.Process.Region.Contains, h1, h2, hp]⟩

/-- The arena's first three slots are readable, not writable (the streams there are the
library's). -/
theorem memM_arena {args : List (List Byte)} (data : List Byte) {a : Nat}
    (h1 : A0 ≤ a) (h2 : a < A0 + 3 * S0) : (memMA args data).permits .read a = true :=
  permits_of_mem (base := A0) (size := 3 * S0) (p := perm true false false) (by simp [memMA, arenaR]) h1 h2 rfl

theorem memM_arena_nw {args : List (List Byte)} (data : List Byte) {a : Nat} (h1 : A0 ≤ a) (h2 : a < A0 + 3 * S0) :
    (memMA args data).permits .write a = false := by
  have hA : A0 = 0x10000000 := rfl
  have hS : S0 = 0x100000 := rfl
  rw [hA] at h1; rw [hA, hS] at h2
  have e1 : stackLo = 0x7ffffffdd000 := by unfold stackLo; rw [sp0_toNat]
  have e2 : libLo = 0x7ffff7e04000 := by unfold libLo; rw [lb0_toNat]
  unfold Memory.permits
  rw [List.any_eq_false]
  intro r hr hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hc1, hc2⟩, hw⟩ := hc
  simp only [memMA, regions0, exeRegions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl) | rfl | rfl | rfl) | rfl | rfl
  all_goals first
    | (simp only [b0_toNat, e1, e2, fs0_toNat] at hc1 hc2; omega)
    | (simp only [stk2R, stk2Lo] at hc1 hc2; omega)
    | (simp [arenaR, perm, Silmaril.Process.Permissions.allows] at hw)

theorem memM_stk2 {args : List (List Byte)} (data : List Byte) {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : stk2Lo ≤ a) (h2 : a < stk2Lo + 0x2000) : (memMA args data).permits acc a = true :=
  permits_of_mem (base := stk2Lo) (size := 0x2000) (p := perm true true false) (by simp [memMA, stk2R]) h1 h2 (by rcases hacc with rfl | rfl <;> rfl)

theorem memM_lib {args : List (List Byte)} (data : List Byte) {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : libLo ≤ a) (h2 : a < libLo + 0x2000) : (memMA args data).permits acc a = true :=
  permits_of_mem (base := libLo) (size := 0x2000) (p := perm true true false) (by simp [memMA, regions0]) h1 h2
    (by rcases hacc with rfl | rfl <;> rfl)

theorem memM_stack {args : List (List Byte)} (data : List Byte) {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : stackLo ≤ a) (h2 : a < stackLo + 8192) : (memMA args data).permits acc a = true :=
  permits_of_mem (base := stackLo) (size := 8192) (p := perm true true false) (by simp [memMA, regions0]) h1 h2
    (by rcases hacc with rfl | rfl <;> rfl)

theorem memM_tlsP {args : List (List Byte)} (data : List Byte) {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : fs0.toNat ≤ a) (h2 : a < fs0.toNat + 0x1000) : (memMA args data).permits acc a = true :=
  permits_of_mem (base := fs0.toNat) (size := 0x1000) (p := perm true true false) (by simp [memMA, regions0]) h1 h2
    (by rcases hacc with rfl | rfl <;> rfl)

/-- The executable's image is readable. -/
theorem memM_img {args : List (List Byte)} (data : List Byte) {a : Nat} (h : ShaImg b0 a) : (memMA args data).permits .read a = true := by
  simp only [ShaImg, b0_toNat] at h
  by_cases ha : a < 0x555555554000 + 0x2000
  · exact permits_of_mem (base := 0x555555554000) (size := 0x2000) (p := perm true false false)
      (by simp [memMA, regions0, exeRegions, b0_toNat]) (by omega) ha rfl
  by_cases hb2 : a < 0x555555554000 + 0x7000
  · exact permits_of_mem (base := 0x555555554000 + 0x2000) (size := 0x5000) (p := perm true false true)
      (by simp [memMA, regions0, exeRegions, b0_toNat]) (by omega) (by omega) rfl
  by_cases hb3 : a < 0x555555554000 + 0x9000
  · exact permits_of_mem (base := 0x555555554000 + 0x7000) (size := 0x2000) (p := perm true false false)
      (by simp [memMA, regions0, exeRegions, b0_toNat]) (by omega) (by omega) rfl
  by_cases hb4 : a < 0x555555554000 + 0xa000
  · exact permits_of_mem (base := 0x555555554000 + 0x9000) (size := 0x1000) (p := perm true false false)
      (by simp [memMA, regions0, exeRegions, b0_toNat]) (by omega) (by omega) rfl
  · exact permits_of_mem (base := 0x555555554000 + 0xa000) (size := 0x1000) (p := perm true true false)
      (by simp [memMA, regions0, exeRegions, b0_toNat]) (by omega) (by omega) rfl

/-- A read of `l` from installed bytes. -/
theorem read_of {m : Memory} {a : Nat} {l : List Byte} (ha : a + l.length < 2 ^ 64)
    (hp : ∀ k < l.length, m.permits .read (a + k) = true)
    (hg : ∀ k (hk : k < l.length), m.bytes.get? (a + k) = some (l[k]'hk)) :
    m.readBytes a l.length = some l :=
  readWith_of_points (by omega) (by omega) fun k hk => ⟨hp k hk, hg k hk⟩

theorem loadN_of_read {m : Memory} {a w : Word} (h : m.readBytes a.toNat 8 = some (leBytes w 8)) :
    loadN m a 8 = some w := by
  simp only [loadN, h, Option.map_some, Silmaril.X86.Ext.leValue_leBytes, Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat < 2 ^ (8 * 8) from w.isLt), Nat.mod_eq_of_lt w.isLt]

theorem slot_file {args : List (List Byte)} (data : List Byte) (k : Nat) (hk : k < 3) (st : St) (hv : Valid st)
    (hget : ∀ j (hj : j < (enc st).length), (bytesMA args data).get? (A0 + k * S0 + j) = some ((enc st)[j]'hj)) :
    fileR (memMA args data) (BitVec.ofNat 64 (A0 + k * S0)) st := by
  have hfn : (BitVec.ofNat 64 (A0 + k * S0)).toNat = A0 + k * S0 := by
    simp only [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; simp only [A0, S0]; omega
  have hl := enc_length st
  have hS := hv.2.2
  have h3 : k * S0 + S0 ≤ 3 * S0 := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  refine ⟨⟨k, by simp only [KS]; omega, hfn⟩, hv, ?_, fun j hj => ?_⟩
  · rw [hfn, ← hl]
    refine read_of (by rw [hl]; simp only [A0, S0] at hS h3 ⊢; omega) (fun j hj => ?_) hget
    rw [hl] at hj
    exact memM_arena (args := args) data (by omega) (by omega)
  · rw [hfn]; exact memM_arena_nw (args := args) data (by omega) (by omega)

theorem file_out {args : List (List Byte)} (data : List Byte) : fileR (memMA args data) outF (outSt 1) := by
  have := slot_file (args := args) data 0 (by decide) (outSt 1) ⟨rfl, by decide, by simp [outSt, S0]⟩ (fun j hj => by
    have hj' : j < 64 := by rw [enc_out_length] at hj; exact hj
    unfold bytesMA
    rw [Memory.install_outside _ _ _ _ (by rw [gateBytes_length, rspT_toNat]; simp only [A0, S0]; omega)]
    rw [Memory.install_outside _ _ _ _ (Or.inl (by simp only [A0, S0]; omega)),
      Memory.install_outside _ _ _ _ (Or.inl (by simp only [A0, S0]; omega))]
    rw [show A0 + 0 * S0 + j = A0 + j by omega]
    exact Memory.install_get _ _ _ _ hj)
  simpa [outF] using this

theorem file_err {args : List (List Byte)} (data : List Byte) : fileR (memMA args data) errF (outSt 2) := by
  have := slot_file (args := args) data 1 (by decide) (outSt 2) ⟨rfl, by decide, by simp [outSt, S0]⟩ (fun j hj => by
    have hj' : j < 64 := by rw [enc_out_length] at hj; exact hj
    unfold bytesMA
    rw [Memory.install_outside _ _ _ _ (by rw [gateBytes_length, rspT_toNat]; simp only [A0, S0]; omega),
      Memory.install_outside _ _ _ _ (Or.inl (by simp only [A0, S0]; omega))]
    rw [show A0 + 1 * S0 + j = (A0 + S0) + j by omega]
    exact Memory.install_get _ _ _ _ hj)
  simpa [errF] using this

theorem file_in {args : List (List Byte)} (data : List Byte) (hd : 64 + data.length ≤ S0) : fileR (memMA args data) inF (stdinSt data) := by
  have hl : (enc (stdinSt data)).length = 64 + data.length := enc_length _
  have := slot_file (args := args) data 2 (by decide) (stdinSt data) ⟨rfl, by simp [stdinSt], hd⟩ (fun j hj => by
    have hj' : j < 64 + data.length := by rw [hl] at hj; exact hj
    have hd' : 64 + data.length ≤ 0x100000 := hd
    unfold bytesMA
    rw [Memory.install_outside _ _ _ _ (by rw [gateBytes_length, rspT_toNat]; simp only [A0, S0]; omega)]
    exact Memory.install_get _ _ _ _ hj)
  simpa [inF] using this


/-! ## The kernel's memory: argument vector, libc's variables, the guard -/

theorem stackLo_eq : stackLo = 0x7ffffffdd000 := by unfold stackLo; rw [sp0_toNat]
theorem libLo_eq : libLo = 0x7ffff7e04000 := by unfold libLo; rw [lb0_toNat]

theorem memW_lib (stk : List Byte) {j : Nat} (hj : j < libPage.length) :
    (memW stk).bytes.get? (libLo + j) = libPage[j]? := by
  rw [libPage_length] at hj
  have hj' : j < libPage.length := by rw [libPage_length]; exact hj
  have hlt : libLo + j < fs0.toNat := by rw [libLo_eq, fs0_toNat]; omega
  unfold memW
  dsimp only
  rw [Memory.install_outside _ _ _ _ (Or.inl hlt),
    Memory.install_get _ _ _ _ hj', List.getElem?_eq_getElem hj']

theorem memW_tls (stk : List Byte) {j : Nat} (hj : j < tlsPage.length) :
    (memW stk).bytes.get? (fs0.toNat + j) = tlsPage[j]? := by
  unfold memW
  dsimp only
  rw [Memory.install_get _ _ _ _ hj, List.getElem?_eq_getElem hj]


theorem mem0_stackP {args : List (List Byte)} {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : stackLo ≤ a) (h2 : a < stackLo + 8192) : (mem0A args).permits acc a = true :=
  permits_of_mem (base := stackLo) (size := 8192) (p := perm true true false) (by simp [mem0A, memW, regions0]) h1 h2
    (by rcases hacc with rfl | rfl <;> rfl)

theorem mem0_libP {args : List (List Byte)} {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : libLo ≤ a) (h2 : a < libLo + 0x2000) : (mem0A args).permits acc a = true :=
  permits_of_mem (base := libLo) (size := 0x2000) (p := perm true true false) (by simp [mem0A, memW, regions0]) h1 h2
    (by rcases hacc with rfl | rfl <;> rfl)

theorem mem0_tlsP {args : List (List Byte)} {acc : Access} (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : fs0.toNat ≤ a) (h2 : a < fs0.toNat + 0x1000) : (mem0A args).permits acc a = true :=
  permits_of_mem (base := fs0.toNat) (size := 0x1000) (p := perm true true false) (by simp [mem0A, memW, regions0]) h1 h2
    (by rcases hacc with rfl | rfl <;> rfl)

theorem stkOf_a00 : stkOf [a00] = pageOf 8192 [(4096, leBytes (BitVec.ofNat 64 1) 8),
    (4104, leBytes (sp0 + BitVec.ofNat 64 64) 8), (argBase, a00 ++ [0#8])] := by
  simp [stkOf]
theorem stk_argv : ((stkOf [a00]).drop 4104).take 8 = leBytes (sp0 + 64#64) 8 := by
  rw [stkOf_a00]; decide +kernel
theorem stk_a0 : ((stkOf [a00]).drop 4160).take 10 = a00 ++ [0#8] := by decide +kernel
theorem lib_in : (libPage.drop 0x16b0).take 8 = leBytes inF 8 := by unfold libPage; decide +kernel
theorem lib_out : (libPage.drop 0x16a8).take 8 = leBytes outF 8 := by unfold libPage; decide +kernel
theorem lib_err : (libPage.drop 0x16a0).take 8 = leBytes errF 8 := by unfold libPage; decide +kernel
theorem tls_g : (tlsPage.drop 0x28).take 8 = leBytes guard0 8 := by unfold tlsPage; decide +kernel

theorem mem0_argv : mem0.readBytes (stackLo + 4104) 8 = some (leBytes (sp0 + 64#64) 8) := by
  rw [← stk_argv]
  exact read_page (fun j hj => memW_stk _ hj)
    (fun j hj => mem0_stackP (Or.inl rfl) (by omega) (by omega)) (by rw [stkOf_length]; decide)
    (by rw [stackLo_eq]; decide)

theorem mem0_a0 : mem0.readBytes (stackLo + 4160) 10 = some (a00 ++ [0#8]) := by
  rw [← stk_a0]
  exact read_page (fun j hj => memW_stk _ hj)
    (fun j hj => mem0_stackP (Or.inl rfl) (by omega) (by omega)) (by rw [stkOf_length]; decide)
    (by rw [stackLo_eq]; decide)

theorem mem0_lib {args : List (List Byte)} {o : Nat} {l : List Byte} (hl : (libPage.drop o).take 8 = l) (ho : o + 8 ≤ 0x2000) :
    (mem0A args).readBytes (libLo + o) 8 = some l := by
  rw [← hl]
  exact read_page (fun j hj => memW_lib _ hj)
    (fun j hj => mem0_libP (Or.inl rfl) (by omega) (by omega)) (by rw [libPage_length]; exact ho)
    (by rw [libLo_eq]; omega)

theorem mem0_guard {args : List (List Byte)} : (mem0A args).readBytes (fs0.toNat + 0x28) 8 = some (leBytes guard0 8) := by
  rw [← tls_g]
  exact read_page (fun j hj => memW_tls _ hj)
    (fun j hj => mem0_tlsP (Or.inl rfl) (by omega) (by omega)) (by rw [tlsPage_length]; decide)
    (by rw [fs0_toNat]; decide)

/-! ## Addresses -/

theorem e_var : (lb0 + 0x2056b0#64).toNat = 0x7ffff7e056b0 := by decide
theorem e_vout : (lb0 + 0x2056a8#64).toNat = 0x7ffff7e056a8 := by decide
theorem e_verr : (lb0 + 0x2056a0#64).toNat = 0x7ffff7e056a0 := by decide
theorem e_pin : (lb0 + 0x205378#64).toNat = 0x7ffff7e05378 := by decide
theorem e_opt : (lb0 + 0x204248#64).toNat = 0x7ffff7e04248 := by decide
theorem e_g : (fs0 + 0x28#64).toNat = 0x7ffff7fb0028 := by decide
theorem e_rsi : (sp0 + 8#64).toNat = 0x7ffffffde008 := by decide
theorem e_a0 : (sp0 + 64#64).toNat = 0x7ffffffde040 := by decide

theorem kept_iff (a : Nat) : Wf.Kept a ↔
    (0x555555554000 ≤ a ∧ a < 0x555555554000 + 0xa188) ∨ (0x7ffffffde000 + 8 ≤ a ∧ a < 0x7ffffffde000 + 4096) ∨
    ((0x7ffff7fb0000 + 0x28 ≤ a ∧ a < 0x7ffff7fb0000 + 0x30) ∨ (0x7ffff7c00000 + 0x2056a0 ≤ a ∧ a < 0x7ffff7c00000 + 0x2056b8)) :=
  Iff.rfl

/-- Reads of `memM` at addresses outside the new ones are those of the kernel's memory. -/
theorem memM_read {args : List (List Byte)} (data : List Byte) (hd : 64 + data.length ≤ S0) {a n : Nat} (h : ∀ k < n, ¬ New (a + k)) :
    (memMA args data).readBytes a n = (mem0A args).readBytes a n :=
  (keepsNew data hd).readBytes h

theorem memM_loadN {args : List (List Byte)} (data : List Byte) (hd : 64 + data.length ≤ S0) {a w : Word}
    (h : ∀ k < 8, ¬ New (a.toNat + k)) (h0 : (mem0A args).readBytes a.toNat 8 = some (leBytes w 8)) :
    loadN (memMA args data) a 8 = some w :=
  loadN_of_read (by rw [memM_read data hd h]; exact h0)


theorem permitted_of {m : Memory} {acc : Access} {a n : Nat} (ha : a + n < 2 ^ 64)
    (hp : ∀ k < n, m.permits acc (a + k) = true) : m.Permitted acc a n := by
  unfold Memory.Permitted
  rw [Memory.checkSpan_iff]
  exact ⟨by simp only [Silmaril.Process.addressLimit]; omega, by simp only [Silmaril.Process.addressLimit]; omega, hp⟩

/-! ## The entry state -/

/-- `main`'s registers: `rsp = rspT`, `argc = 1`, `argv = sp0 + 8`, `envp = a3`. -/
def coreM (f a3 : Word) : State :=
  ⟨fun r => if r = .rsp then rspT else if r = .rdi then 1#64 else if r = .rsi then sp0 + 8#64
    else if r = .rdx then a3 else 0, f, ⟨none, none, none, none, none, none⟩, fs0⟩

/-- **`main`'s entry state.** -/
def entM (data : List Byte) (f a3 : Word) (g : Ghost) : PState := ⟨⟨coreM f a3, memM data⟩, g⟩

section
variable (f a3 : Word)
theorem coreM_rsp : (coreM f a3).read .rsp = rspT := by simp [coreM, State.read]
theorem coreM_rdi : (coreM f a3).read .rdi = 1#64 := by simp [coreM, State.read]
theorem coreM_rsi : (coreM f a3).read .rsi = sp0 + 8#64 := by simp [coreM, State.read]
theorem coreM_rdx : (coreM f a3).read .rdx = a3 := by simp [coreM, State.read]
end

/-- The library's own variables `main`'s head writes: `program_invocation_name`'s pin and `optind`. -/
def Cm (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (a : Nat) : Prop :=
  PinR lb0 a ∨ OptR (E0 fs) a

theorem pin_iff (a : Nat) : PinR lb0 a ↔ 0x7ffff7e05378 ≤ a ∧ a < 0x7ffff7e05378 + 8 := by
  simp only [PinR, e_pin]
theorem opt_iff (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (a : Nat) :
    OptR (E0 fs) a ↔ 0x7ffff7e04248 ≤ a ∧ a < 0x7ffff7e04248 + 4 := by
  show (lb0 + 0x204248#64).toNat ≤ a ∧ a < (lb0 + 0x204248#64).toNat + 4 ↔ _
  rw [e_opt]
theorem var_iff (a : Nat) : VarR lb0 a ↔ 0x7ffff7e056a0 ≤ a ∧ a < 0x7ffff7e056a0 + 16 := by
  simp only [VarR, e_verr]
theorem img_iff (a : Nat) : ShaImg b0 a ↔ 0x555555554000 ≤ a ∧ a < 0x555555554000 + 0xa188 := by
  simp only [ShaImg, b0_toNat]
theorem args_iff (a : Nat) : Wf.args a ↔ 0x7ffffffde000 + 8 ≤ a ∧ a < 0x7ffffffde000 + 4096 := Iff.rfl

theorem not_new_lib {a : Nat} (h1 : 0x7ffff7e04000 ≤ a) (h2 : a < 0x7ffff7e06000) : ¬ New a := by
  simp only [New, A0, S0, stk2Lo]; omega
theorem not_new_kept {a : Nat} (h1 : 0x7ffff7000000 ≤ a) (h2 : a < 0x7ffffffdb000) : ¬ New a := by
  simp only [New, A0, S0, stk2Lo]; omega
theorem not_new_hi {a : Nat} (h1 : 0x7ffffffdd000 ≤ a) : ¬ New a := by
  simp only [New, A0, S0, stk2Lo]; omega

theorem lib_read {args : List (List Byte)} (data : List Byte) (hd : 64 + data.length ≤ S0) {o : Nat} {w : Word}
    (hl : (libPage.drop o).take 8 = leBytes w 8) (ho : o + 8 ≤ 0x2000) :
    loadN (memMA args data) (BitVec.ofNat 64 (0x7ffff7e04000 + o)) 8 = some w := by
  have hn : (BitVec.ofNat 64 (0x7ffff7e04000 + o)).toNat = 0x7ffff7e04000 + o := by
    simp only [BitVec.toNat_ofNat]; omega
  refine memM_loadN data hd (fun k hk => by rw [hn]; exact not_new_lib (by omega) (by omega)) ?_
  rw [hn, ← libLo_eq]
  exact mem0_lib hl ho

set_option maxRecDepth 100000 in
/-- **`MainLib` holds at `entM`.** -/
theorem mainLib_entM (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (data : List Byte) (hd : 64 + data.length ≤ S0) (f a3 : Word) (g : Ghost) :
    MainLib (E0 fs) Wf b0 lb0 (Cm fs) inF (entM data f a3 g) (sp0 + 64#64) a00 data guard0 := by
  have hrsp : (entM data f a3 g).m.core.read .rsp = rspT := coreM_rsp f a3
  have hrsi : (entM data f a3 g).m.core.read .rsi = sp0 + 8#64 := coreM_rsi f a3
  have hrdi : (entM data f a3 g).m.core.read .rdi = 1#64 := coreM_rdi f a3
  have hfs : (entM data f a3 g).m.core.fsBase = fs0 := rfl
  have hm : (entM data f a3 g).m.memory = memM data := rfl
  have hvar : lb0 + 0x2056b0#64 = BitVec.ofNat 64 (0x7ffff7e04000 + 0x16b0) := by decide
  have hvout : lb0 + 0x2056a8#64 = BitVec.ofNat 64 (0x7ffff7e04000 + 0x16a8) := by decide
  have hverr : lb0 + 0x2056a0#64 = BitVec.ofNat 64 (0x7ffff7e04000 + 0x16a0) := by decide
  refine
    { lo := by rw [hrsp]; show A0 + K0 * S0 + 4096 ≤ rspT.toNat; rw [rspT_toNat]; simp only [A0, K0, S0]; omega
      env := by
       rw [hm]
       exact
        { out := file_out data
          err := file_err data
          inp := file_in data hd
          vars :=
            { out := by rw [hvout]; exact lib_read data hd lib_out (by decide)
              err := by rw [hverr]; exact lib_read data hd lib_err (by decide)
              kept := fun k hk => by rw [kept_iff, e_verr]; omega
              bound := by rw [e_verr]; omega }
          np := fun a h => by
            rcases h with h | h
            · refine ⟨fun hA => ?_, memM_img data h⟩
              have hA' : Arena a := hA
              rw [img_iff] at h; simp only [Arena, A0, K0, S0] at hA'; omega
            · have hb : 0x7ffff7e04000 ≤ a ∧ a < 0x7ffff7e06000 := by
                rcases h with h | h
                · rw [pin_iff] at h; omega
                · rw [opt_iff] at h; omega
              refine ⟨fun hA => ?_, memM_lib data (Or.inl rfl) (by rw [libLo_eq]; omega) (by rw [libLo_eq]; omega)⟩
              have hA' : Arena a := hA
              simp only [Arena, A0, K0, S0] at hA'; omega
          wr := fun a h => by
            have hb : 0x7ffff7e04000 ≤ a ∧ a < 0x7ffff7e06000 := by
              rcases h with h | h
              · rw [pin_iff] at h; omega
              · rw [opt_iff] at h; omega
            exact memM_lib data (Or.inr rfl) (by rw [libLo_eq]; omega) (by rw [libLo_eq]; omega) }
      hC := fun a h => by
        left; rw [hrsp, rspT_toNat]
        rcases h with h | h
        · rw [pin_iff] at h; omega
        · rw [opt_iff] at h; omega
      pinC := fun a h => Or.inl h
      pinK := fun a h hk => by rw [pin_iff] at h; rw [kept_iff] at hk; omega
      optC := fun a h => Or.inr h
      optK := fun a h hk => by rw [opt_iff] at h; rw [kept_iff] at hk; omega
      optL := fun a h => by rw [opt_iff] at h; rw [hrsp, rspT_toNat]; omega
      opt := by show (lb0 + 0x204248#64).toNat + 4 < 2 ^ 64; rw [e_opt]; omega
      lbB := by rw [lb0_toNat]; omega
      imgVar := fun a h hv => by rw [img_iff] at h; rw [var_iff] at hv; omega
      argsImg := fun a h hi => by rw [args_iff] at h; rw [img_iff] at hi; omega
      argc := by rw [hrdi]; decide
      argv := fun m hk i hi => by
        rw [hm] at hk; rw [hrsi]
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        refine ⟨sp0 + 64#64, ?_, ?_⟩
        · rw [show sp0 + 8#64 + BitVec.ofNat 64 (8 * 0) = sp0 + 8#64 by decide,
            loadN_keeps hk (fun k hk' => by rw [args_iff, e_rsi]; omega)]
          refine memM_loadN data hd (fun k hk' => by rw [e_rsi]; exact not_new_hi (by omega)) ?_
          rw [e_rsi, show (0x7ffffffde008 : Nat) = stackLo + 4104 by rw [stackLo_eq]]
          exact mem0_argv
        · refine cstr_keeps hk ⟨by show ∀ x ∈ a00, x ≠ 0; decide, ?_⟩ (fun j hj => by
            rw [args_iff, e_a0]; simp only [List.getElem_cons_zero, a00, List.length_cons, List.length_nil] at hj; omega)
          show (memM data).readBytes (sp0 + 64#64).toNat 10 = some (a00 ++ [0#8])
          rw [memM_read data hd (fun k hk' => by rw [e_a0]; exact not_new_hi (by omega)), e_a0,
            show (0x7ffffffde040 : Nat) = stackLo + 4160 by rw [stackLo_eq]]
          exact mem0_a0
      argv0 := by
        rw [hm, hrsi]
        refine memM_loadN data hd (fun k hk' => by rw [e_rsi]; exact not_new_hi (by omega)) ?_
        rw [e_rsi, show (0x7ffffffde008 : Nat) = stackLo + 4104 by rw [stackLo_eq]]
        exact mem0_argv
      argv0k := fun k hk => by rw [hrsi, kept_iff, e_rsi]; omega
      a0s := by
        rw [hm]
        refine ⟨by decide, ?_⟩
        show (memM data).readBytes (sp0 + 64#64).toNat 10 = some (a00 ++ [0#8])
        rw [memM_read data hd (fun k hk' => by rw [e_a0]; exact not_new_hi (by omega)), e_a0,
          show (0x7ffffffde040 : Nat) = stackLo + 4160 by rw [stackLo_eq]]
        exact mem0_a0
      a0k := fun j hj => by
        rw [kept_iff, e_a0]; simp only [a00, List.length_cons, List.length_nil] at hj; omega
      a0nz := by decide
      noSlash := by decide
      guard := by
        rw [hm, hfs]
        refine memM_loadN data hd (fun k hk' => by rw [e_g]; exact not_new_kept (by omega) (by omega)) ?_
        rw [e_g, show (0x7ffff7fb0028 : Nat) = fs0.toNat + 0x28 by rw [fs0_toNat]]
        exact mem0_guard
      guardk := fun j hj => by rw [hfs, kept_iff, e_g]; omega
      guardImg := fun j hj h => by rw [hfs, img_iff, e_g] at h; omega
      var := by rw [hm, hvar]; exact lib_read data hd lib_in (by decide)
      vark := fun j hj => by rw [kept_iff, e_var]; omega
      varImg := fun j hj h => by rw [img_iff, e_var] at h; omega
      fi0 := by decide
      fiO := by show inF ≠ outF; decide
      fiE := by show inF ≠ errF; decide
      avHi := by rw [hrsp, hrsi, rspT_toNat, e_rsi]; omega
      av := by rw [hrsi, e_rsi]; omega
      avA := fun j hj => by rw [hrsi, args_iff, e_rsi]; omega
      avR := by
       rw [hm, hrsi]
       exact permitted_of (by rw [e_rsi]; omega) fun k hk => memM_stack data (Or.inl rfl)
        (by rw [e_rsi, stackLo_eq]; omega) (by rw [e_rsi, stackLo_eq]; omega)
      avW := by
       rw [hm, hrsi]
       exact permitted_of (by rw [e_rsi]; omega) fun k hk => memM_stack data (Or.inr rfl)
        (by rw [e_rsi, stackLo_eq]; omega) (by rw [e_rsi, stackLo_eq]; omega)
      avVar := fun j hj h => by rw [hrsi, var_iff, e_rsi] at h; omega
      avIn := by rw [hrsi, e_var, e_rsi]; omega
      avG := by rw [hfs, hrsi, e_g, e_rsi]; omega }

/-- `main` is entered at `entM`: the gate word on a fresh aligned stack, the kept memory and
`fsBase` as the kernel left them. -/
theorem enters_entM (data : List Byte) (hd : 64 + data.length ≤ S0) (u : PState) (f a3 : Word) (g : Ghost)
    (hu : Keeps Wf.Kept (s0 [a00]).m.memory u.m.memory) (hfs : u.m.core.fsBase = fs0) :
    Enters Wf u (entM data f a3 g) f := by
  have hrsp : (entM data f a3 g).m.core.read .rsp = rspT := coreM_rsp f a3
  refine ⟨rfl, by rw [hrsp, rspT_toNat], ?_, ?_, ?_, hfs.symm⟩
  · rw [hrsp]
    show (memM data).readBytes rspT.toNat 8 = some gateBytes
    rw [← gateBytes_length]
    refine read_of (by rw [gateBytes_length, rspT_toNat]; omega)
      (fun k hk => memM_stk2 data (Or.inl rfl) (by rw [rspT_toNat]; simp only [stk2Lo]; omega)
        (by rw [gateBytes_length] at hk; rw [rspT_toNat]; simp only [stk2Lo]; omega)) (fun k hk => ?_)
    exact Memory.install_get _ _ _ _ hk
  · rw [hrsp]
    refine ⟨by rw [rspT_toNat]; omega, by rw [rspT_toNat]; omega, fun a h1 h2 => ?_⟩
    rw [rspT_toNat] at h1 h2
    refine ⟨memM_stk2 data (Or.inl rfl) (by simp only [stk2Lo]; omega) (by simp only [stk2Lo]; omega),
      memM_stk2 data (Or.inr rfl) (by simp only [stk2Lo]; omega) (by simp only [stk2Lo]; omega), fun hk => ?_⟩
    rw [kept_iff] at hk; omega
  · exact (Keeps.symm' hu).trans ((keepsNew data hd).mono fun a h => kept_not_new h)

/-- **`Task.mainLibReach` holds**: from every gate state with the kernel's kept memory and
`fsBase`, `main` can be entered with `Astdin` (standard input fitting a stream slot). -/
theorem task_mainLibReach (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (data : List Byte) : Task.mainLibReach fs data := by
  intro hd u f a3 g _ hu hfs
  exact ⟨entM data f a3 g, enters_entM data hd u f a3 g hu hfs, coreM_rdi f a3, coreM_rsi f a3,
    coreM_rdx f a3, rfl, Cm fs, inF, sp0 + 64#64, guard0, mainLib_entM fs data hd f a3 g⟩

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
