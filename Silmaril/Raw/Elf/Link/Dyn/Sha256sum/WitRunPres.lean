module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitRunMem

/-! # GNU `sha256sum` witness: every import contract keeps the invariant

`entry_inv`: an outcome of any contract of the concrete table (`table0 fs`), from a state of
`Inv` where the call does not stop (so its precondition holds), is again in `Inv`: the frames
(`NoMap`, `NoNewStream`) keep the heap zone and the slots, `malloc` and `fopen` add their block
or stream together with their counter.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.RelIsa (Res)
open Silmaril.X86.Ext (loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total
open Silmaril.Elf.Link.Dyn.Imports

section
variable {s t : PState}

theorem inv_frame (hI : Inv s) (hj : t.g.jobs = s.g.jobs) (ha : t.g.allocs = s.g.allocs)
    (hh : t.g.heap = s.g.heap) (hf : t.g.files = s.g.files)
    (hz : ∀ x, x < A0 → t.m.memory.permits .read x = true → s.m.memory.permits .read x = true)
    (hs : ∀ f st, fileR t.m.memory f st → ∃ st0, fileR s.m.memory f st0) : Inv t :=
  inv_of_frame hI ⟨hj, ha, hh, hf, hz, hs⟩

theorem inv_lib {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} {W : World}
    {fp : Nat → Prop} (hI : Inv s) (h : LibRet (E0 fs) W fp s t)
    (hfpR : ∀ x, fp x → x < A0 → s.m.memory.permits .read x = true) (hfpA : ∀ x, fp x → ¬ Arena x)
    (hj : t.g.jobs = s.g.jobs) (ha : t.g.allocs = s.g.allocs) (hh : t.g.heap = s.g.heap)
    (hf : t.g.files = s.g.files) : Inv t :=
  let ⟨hz, hs⟩ := frame_libRet h hfpR hfpA
  inv_frame hI hj ha hh hf hz hs

theorem inv_lib0 {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} {W : World}
    (hI : Inv s) (h : LibRet (E0 fs) W (fun _ => False) s t) (hg : t.g = s.g) : Inv t :=
  inv_lib hI h (fun _ h => h.elim) (fun _ h => h.elim) (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])

theorem inv_out {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} {W : World}
    (hI : Inv s) (h : LibRet (E0 fs) W (fun _ => False) s t) (hg : GhostOut s t) : Inv t :=
  inv_lib hI h (fun _ h => h.elim) (fun _ h => h.elim) hg.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2

theorem inv_noMap {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} (hI : Inv s)
    (hm : NoMap (E0 fs) (fun _ => False) s t) (hn : NoNewStream (E0 fs) (fun _ => False) s t)
    (hj : t.g.jobs = s.g.jobs) (ha : t.g.allocs = s.g.allocs) (hh : t.g.heap = s.g.heap)
    (hf : t.g.files = s.g.files) : Inv t :=
  let ⟨hz, hs⟩ := frame_noMap hm hn
  inv_frame hI hj ha hh hf hz hs

theorem inv_jobs (hj : JobsOK t.g.jobs) (hnm : ¬ InMain t.g) : Inv t := ⟨hj, fun h => absurd h hnm⟩

theorem jobs_exit (w : Word) : JobsOK [Job.exit w] := by simp [JobsOK]
theorem not_main_exit {g : Ghost} {w : Word} (h : g.jobs = [Job.exit w]) : ¬ InMain g := by
  rintro ⟨js, hj⟩; rw [h] at hj; cases hj

end

/-! ## `malloc` and `fopen` -/

theorem inv_malloc {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} {W : World}
    {s t : PState} (hI : Inv s) (hs : ¬ mallocStep (E0 fs) W s .stop)
    (h : mallocStep (E0 fs) W s (.ok t)) : Inv t := by
  obtain ⟨-, hL, hg, -, hd⟩ := contract_post h hs
  have hj : t.g.jobs = s.g.jobs := by rw [hg]
  have hf : t.g.files = s.g.files := by rw [hg]
  obtain ⟨-, -, -, -, -, -, hmap, hnew⟩ := hL
  have hstr : ∀ f st, fileR t.m.memory f st → ∃ st0, fileR s.m.memory f st0 := by
    intro f st hft
    rcases hnew f st hft with h | h
    · exact h
    · exfalso
      have hsl := slot_lt hft.1
      have hS : 0 < S0 := by decide
      obtain ⟨hnz, h1, h2⟩ := h f.toNat ⟨le_refl _, by omega⟩
      rcases hd with ⟨h0, -⟩ | ⟨-, -, -, -, -, -, hb⟩
      · exact hnz h0
      · exact (hb f.toNat h1 h2).1 ⟨by omega, by omega⟩
  refine ⟨by unfold JobsOK; rw [hj]; exact hI.1, fun hm => ?_⟩
  have hm' : InMain s.g := by obtain ⟨js, hjs⟩ := hm; exact ⟨js, by rw [← hj, hjs]⟩
  obtain ⟨⟨L, hLl, hsz, hcov⟩, ⟨K, hK, hmem⟩⟩ := hI.2 hm'
  refine ⟨?_, ⟨K, by rw [hf]; exact hK, fun f st hft => ?_⟩⟩
  · rcases hd with ⟨h0, -, hal, hhp, -⟩ | ⟨hnz, hal, hhp, -, -, -, hb⟩
    · refine ⟨L, by rw [hal]; exact hLl, fun b hb => by rw [hhp]; exact hsz b hb, fun x hx hr => ?_⟩
      refine hcov x hx ?_
      by_contra hc
      have hs0 : s.m.memory.permits .read x = false := by simpa using hc
      have := hmap x (fun h => h.1 h0) hs0 (not_arena_low hx) .read
      rw [this, hs0] at hr; cases hr
    · refine ⟨((t.m.core.read .rax).toNat, (s.m.core.read .rdi).toNat) :: L, by simp; rw [hal]; omega,
        fun b hb => ?_, fun x hx hr => ?_⟩
      · simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · rw [hhp]; omega
        · have := hsz b hb; rw [hhp]; omega
      · by_cases hfp : t.m.core.read .rax ≠ 0#64 ∧ (t.m.core.read .rax).toNat ≤ x ∧
            x < (t.m.core.read .rax).toNat + (s.m.core.read .rdi).toNat
        · exact ⟨_, List.mem_cons_self, hfp.2.1, hfp.2.2⟩
        · have hsr : s.m.memory.permits .read x = true := by
            by_contra hc
            have hs0 : s.m.memory.permits .read x = false := by simpa using hc
            have := hmap x hfp hs0 (not_arena_low hx) .read
            rw [this, hs0] at hr; cases hr
          obtain ⟨b, hb, h1, h2⟩ := hcov x hx hsr
          exact ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩
  · obtain ⟨st0, h0⟩ := hstr f st hft
    exact hmem f st0 h0

theorem inv_fopen {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} {W : World}
    {s t : PState} (hI : Inv s) (hs : ¬ fopenStep (E0 fs) W s .stop)
    (h : fopenStep (E0 fs) W s (.ok t)) : Inv t := by
  obtain ⟨⟨-, ⟨p, hp⟩, -⟩, hL, hg, -, hd⟩ := contract_post h hs
  have hj : t.g.jobs = s.g.jobs := by rw [hg]
  have hal : t.g.allocs = s.g.allocs := by rw [hg]
  have hhp : t.g.heap = s.g.heap := by rw [hg]
  have hcase : (t.m.core.read .rax = 0#64 ∧ t.g.files = s.g.files) ∨
      ∃ st, (E0 fs).S.file t.m.memory (t.m.core.read .rax) st ∧ t.m.core.read .rax ≠ 0#64 ∧
        t.g.files = s.g.files + 1 := by
    have hd' := hd p hp
    split at hd'
    · exact Or.inl ⟨hd'.1, hd'.2.1⟩
    · rcases hd' with ⟨h0, -, hfi⟩ | ⟨fd, hfile, hnz, -, -, hfi, -, -⟩
      · exact Or.inl ⟨h0, hfi⟩
      · exact Or.inr ⟨_, hfile, hnz, hfi⟩
  obtain ⟨-, -, -, -, -, -, hmap, hnew⟩ := hL
  have hzone : ∀ x, x < A0 → t.m.memory.permits .read x = true → s.m.memory.permits .read x = true := by
    intro x hx hr
    by_contra hc
    have hs0 : s.m.memory.permits .read x = false := by simpa using hc
    have hfp : ¬ (t.m.core.read .rax ≠ 0#64 ∧ (E0 fs).S.foot t.m.memory (t.m.core.read .rax) x) := by
      rintro ⟨hnz, hft⟩
      rcases hcase with ⟨h0, -⟩ | ⟨st, hfile, -, -⟩
      · exact hnz h0
      · have := (E0 fs).S.foot_priv _ _ _ _ hfile hft
        exact not_arena_low hx this
    have := hmap x hfp hs0 (not_arena_low hx) .read
    rw [this, hs0] at hr; cases hr
  refine ⟨by unfold JobsOK; rw [hj]; exact hI.1, fun hm => ?_⟩
  have hm' : InMain s.g := by obtain ⟨js, hjs⟩ := hm; exact ⟨js, by rw [← hj, hjs]⟩
  obtain ⟨⟨L, hLl, hsz, hcov⟩, ⟨K, hK, hmem⟩⟩ := hI.2 hm'
  refine ⟨⟨L, by rw [hal]; exact hLl, fun b hb => by rw [hhp]; exact hsz b hb,
    fun x hx hr => hcov x hx (hzone x hx hr)⟩, ?_⟩
  rcases hcase with ⟨h0, hfi⟩ | ⟨st1, hfile, hnz, hfi⟩
  · refine ⟨K, by rw [hfi]; exact hK, fun f st hft => ?_⟩
    rcases hnew f st hft with h | h
    · obtain ⟨st0, h0'⟩ := h; exact hmem f st0 h0'
    · exfalso
      have hsl := slot_lt hft.1
      exact (h f.toNat ⟨le_refl _, by omega⟩).1 h0
  · obtain ⟨k, hk, hke⟩ := hfile.1
    refine ⟨k :: K, by simp; rw [hfi]; omega, fun f st hft => ?_⟩
    rcases hnew f st hft with h | h
    · obtain ⟨st0, h0'⟩ := h
      obtain ⟨k', hk', hk'S, he⟩ := hmem f st0 h0'
      exact ⟨k', List.mem_cons_of_mem _ hk', hk'S, he⟩
    · have hsl := slot_lt hft.1
      obtain ⟨-, hft'⟩ := h f.toNat ⟨le_refl _, by omega⟩
      have hin := foot_in_slot hfile hft'
      have hfe : f = t.m.core.read .rax := by
        by_contra hne
        have := slot_disjoint hfile.1 hft.1 (Ne.symm hne) (le_refl _) (by have : 0 < S0 := (by decide); omega)
        omega
      refine ⟨k, List.mem_cons_self, hk, ?_⟩
      rw [hfe]
      apply BitVec.eq_of_toNat_eq
      rw [hke, slotW_toNat (by unfold KS at hk; unfold K0; omega)]


/-! ## Every contract of the table -/

theorem framed_c {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} {W : World}
    {fp : PState → Nat → Prop} {c : PState → Res PState → Prop} {s : PState}
    (hs : ¬ framed (E0 fs) W fp c s .stop) : ¬ c s .stop :=
  fun hc => hs ⟨hc, fun _ t ht => (by cases ht), fun t ht => (by cases ht)⟩

theorem inv_framed {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} {W : World}
    {fp : PState → Nat → Prop} {c : PState → Res PState → Prop} {s t : PState} (hI : Inv s)
    (h : framed (E0 fs) W fp c s (.ok t)) (hj : t.g.jobs = s.g.jobs) (ha : t.g.allocs = s.g.allocs)
    (hh : t.g.heap = s.g.heap) (hf : t.g.files = s.g.files) : Inv t :=
  inv_noMap hI (h.2.2 t rfl).1 (h.2.2 t rfl).2 hj ha hh hf

theorem readable_at {m : Memory} {acc : Access} {a n : Nat} (h : m.Permitted acc a n) :
    ∀ x, a ≤ x → x < a + n → m.permits acc x = true := by
  intro x h1 h2
  unfold Memory.Permitted at h; rw [Memory.checkSpan_iff] at h
  have := h.2.2 (x - a) (by omega)
  rwa [show a + (x - a) = x by omega] at this

theorem optA_out {x : Nat} (h1 : (lb0 + 0x204248#64).toNat ≤ x) : ¬ Arena x := by
  rw [e_opt] at h1; unfold Arena A0 K0 S0; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Every contract of the concrete table keeps the invariant.** -/
theorem entry_inv {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult}
    {e : Name × (PState → Res PState → Prop)} (he : e ∈ table0 fs) {s t : PState}
    (hI : Inv s) (h : e.2 s (.ok t)) (hs : ¬ e.2 s .stop) : Inv t := by
  simp only [table0, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only at h hs
  · -- strrchr
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_lib0 hI hL hg
  · obtain ⟨-, -, -, hg⟩ := contract_post h.1 (framed_c hs)
    exact inv_framed hI h (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · obtain ⟨-, -, -, hg⟩ := contract_post h.1 (framed_c hs)
    exact inv_framed hI h (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · obtain ⟨-, -, -, hg⟩ := contract_post h.1 (framed_c hs)
    exact inv_framed hI h (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · -- __cxa_atexit
    obtain ⟨-, -, -, hg⟩ := contract_post h.1 (framed_c hs)
    exact inv_framed hI h (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · -- setvbuf
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_lib0 hI hL hg
  · -- getopt_long
    obtain ⟨⟨-, hr, -, -⟩, hL, hg, -⟩ := contract_post h hs
    exact inv_lib hI hL (fun x hx _ => readable_at hr x hx.1 hx.2) (fun x hx => optA_out hx.1)
      (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · -- clearerr_unlocked
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_lib0 hI hL hg
  · -- lseek
    obtain ⟨-, hL, -, hg, -⟩ := contract_post h hs; exact inv_lib0 hI hL hg
  · exact inv_fopen hI hs h
  · -- posix_fadvise
    obtain ⟨-, hL, -, hg, -⟩ := contract_post h hs; exact inv_lib0 hI hL hg
  · exact inv_malloc hI hs h
  · -- free
    obtain ⟨-, ⟨-, -, -, -, -, -, hm, hn⟩, hg, -⟩ := contract_post h hs
    exact inv_noMap hI hm hn (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · -- __fread_unlocked_chk
    have hcond : (s.m.core.read .rdx).toNat * (s.m.core.read .rcx).toNat ≤ (s.m.core.read .rsi).toNat := by
      by_contra hc; exact hs fun h' => absurd h' hc
    obtain ⟨⟨-, ⟨st, hst⟩, -, -, hr, hnp, -⟩, hq⟩ := contract_post (h hcond) (fun h' => hs fun _ => h')
    have hq' := hq st hst
    have hlen := readSt_fst_length st ((s.m.core.read .rdx).toNat * (s.m.core.read .rcx).toNat)
    rcases hR : readSt st ((s.m.core.read .rdx).toNat * (s.m.core.read .rcx).toNat) with ⟨d, st'⟩
    rw [hR] at hq' hlen
    obtain ⟨hL, hg, -⟩ := hq'
    exact inv_lib hI hL (fun x hx _ => readable_at hr x hx.1 (by simp only at hlen; omega))
      (fun x hx => hnp x hx.1 (by simp only at hlen; omega)) (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · obtain ⟨-, -, -, -, hg⟩ := contract_post h.1 (framed_c hs)
    exact inv_framed hI h (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · obtain ⟨-, -, -, -, hg⟩ := contract_post h.1 (framed_c hs)
    exact inv_framed hI h (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · obtain ⟨-, -, -, -, hg⟩ := contract_post h.1 (framed_c hs)
    exact inv_framed hI h (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg])
  · -- fileno
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_lib0 hI hL hg
  · -- __freading
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_lib0 hI hL hg
  · -- fflush
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_out hI hL hg
  · -- fclose
    obtain ⟨-, hL, hj, -, -, -, -, ha, hh, hf, -⟩ := contract_post h hs
    exact inv_lib hI hL (fun _ h => h.elim) (fun _ h => h.elim) hj ha hh hf
  · -- __fpending
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_lib0 hI hL hg
  · -- __printf_chk
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_out hI hL hg
  · -- __overflow
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_out hI hL hg
  · -- fputs_unlocked
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_out hI hL hg
  · -- strcspn
    obtain ⟨-, hL, hg, -⟩ := contract_post h hs; exact inv_lib0 hI hL hg

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
