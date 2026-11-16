module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitMain

/-! # GNU `sha256sum` witness: the resource invariant of the concrete process

While `main` runs (`InMain`), the concrete process keeps two facts about the library's resources:

* `InvZ`: the mapped memory below the arena is covered by at most `allocs` blocks (`malloc`'s),
  each of at most `heap` bytes (the ghost counters);
* `InvS`: the streams sit in at most `3 + files` slots (`stdin`/`stdout`/`stderr` and the ones
  `fopen` opened).

From them every request within the resource bounds can be met (`zone_room`: a free window below
the arena, by pigeonhole over `2 · allocs + 1` windows; `slot_room`: a free slot).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total

/-- Slot `k`'s address. -/
def slotW (k : Nat) : Word := BitVec.ofNat 64 (A0 + k * S0)

/-- The blocks below the arena. -/
def InvZ (s : PState) : Prop :=
  ∃ L : List (Nat × Nat), L.length ≤ s.g.allocs ∧ (∀ b ∈ L, b.2 ≤ s.g.heap) ∧
    ∀ x, x < A0 → s.m.memory.permits .read x = true → ∃ b ∈ L, b.1 ≤ x ∧ x < b.1 + b.2

/-- The occupied slots. -/
def InvS (s : PState) : Prop :=
  ∃ K : List Nat, K.length ≤ 3 + s.g.files ∧
    ∀ f st, fileR s.m.memory f st → ∃ k ∈ K, k < KS ∧ f = slotW k

/-- `main`'s return job is never queued behind another job. -/
def JobsOK (l : List Job) : Prop := Job.exitRax ∉ l.tail

/-- **The invariant**: the job queue's shape, and the resources while `main` runs. -/
def Inv (s : PState) : Prop := JobsOK s.g.jobs ∧ (InMain s.g → InvZ s ∧ InvS s)

theorem exists_not_mem (K : List Nat) (n : Nat) (h : K.length < n) : ∃ j < n, j ∉ K := by
  by_contra hc
  have hsub : List.range n ⊆ K := fun x hx => by
    by_contra hx'; exact hc ⟨x, List.mem_range.mp hx, hx'⟩
  have := ((List.nodup_range).subperm hsub).length_le
  simp at this
  omega

theorem slotW_toNat {k : Nat} (hk : k < K0) : (slotW k).toNat = A0 + k * S0 := by
  simp only [slotW, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have : k * S0 < K0 * S0 := Nat.mul_lt_mul_of_pos_right hk (by decide)
  unfold A0 K0 S0 at *; omega

theorem slotW_inj {k k' : Nat} (hk : k < K0) (hk' : k' < K0) (h : slotW k = slotW k') : k = k' := by
  have := congrArg BitVec.toNat h
  rw [slotW_toNat hk, slotW_toNat hk'] at this
  unfold S0 at this
  omega

/-- **A free slot** when fewer than `mOpen` streams were opened. -/
theorem slot_room {s : PState} (h : InvS s) (hf : s.g.files < mOpen) :
    ∃ k < KS, ∀ st0, ¬ fileR s.m.memory (BitVec.ofNat 64 (A0 + k * S0)) st0 := by
  obtain ⟨K, hK, hmem⟩ := h
  obtain ⟨j, hj, hjK⟩ := exists_not_mem K KS (by unfold mOpen at hf; unfold KS; omega)
  refine ⟨j, hj, fun st0 h0 => ?_⟩
  obtain ⟨k, hk, hkS, he⟩ := hmem _ st0 h0
  have : j = k := slotW_inj (by unfold KS at hj; unfold K0; omega) (by unfold KS at hkS; unfold K0; omega) he
  exact hjK (this ▸ hk)

/-- The windows of the zone below the arena. -/
def zZ : Nat := 0x1000

theorem window_of {b1 b2 x j : Nat} (hb : b2 ≤ mHeap) (h1 : b1 ≤ x) (h2 : x < b1 + b2)
    (hx1 : zZ + j * mHeap ≤ x) (hx2 : x < zZ + (j + 1) * mHeap) :
    j = (b1 - zZ) / mHeap ∨ j = (b1 - zZ) / mHeap + 1 := by
  unfold zZ mHeap at *
  omega

/-- **Room for a block below the arena** when fewer than `mAllocs` blocks of `heap ≤ mHeap - n`
bytes were handed out. -/
theorem zone_room {s : PState} {n : Nat} (h : InvZ s) (ha : s.g.allocs < mAllocs) (hn : s.g.heap + n ≤ mHeap)
    (hW : ∀ x, x < A0 → ¬ Wf.Kept x) :
    ∃ a, 0 < a ∧ a + n + 0x100000 ≤ A0 ∧
      ∀ x, a ≤ x → x < a + n → s.m.memory.permits .read x = false ∧ ¬ Wf.Kept x := by
  obtain ⟨L, hL, hsz, hcov⟩ := h
  let K := L.flatMap fun b => [(b.1 - zZ) / mHeap, (b.1 - zZ) / mHeap + 1]
  have hKl : ∀ L' : List (Nat × Nat),
      (L'.flatMap fun b => [(b.1 - zZ) / mHeap, (b.1 - zZ) / mHeap + 1]).length = 2 * L'.length := by
    intro L'
    induction L' with
    | nil => rfl
    | cons b L' ih => rw [List.flatMap_cons, List.length_append, ih]; simp; omega
  obtain ⟨j, hj, hjK⟩ := exists_not_mem K 9 (by rw [hKl L]; unfold mAllocs at ha; omega)
  refine ⟨zZ + j * mHeap, by unfold zZ; omega, by unfold zZ mHeap A0 at *; omega, fun x h1 h2 => ⟨?_, hW x
    (by unfold zZ mHeap A0 at *; omega)⟩⟩
  cases hr : s.m.memory.permits .read x with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨b, hb, hb1, hb2⟩ := hcov x (by unfold zZ mHeap A0 at *; omega) hr
    have hbs : b.2 ≤ mHeap := by have := hsz b hb; omega
    have hw := window_of hbs hb1 hb2 h1 (by unfold mHeap at *; omega)
    apply hjK
    simp only [K, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨b, hb, hw⟩


/-! ## Keeping the invariant -/

theorem contract_post {pre : Prop} {post : PState → Prop} {t : PState}
    (h : Contract pre post (.ok t)) (hs : ¬ Contract pre post .stop) : pre ∧ post t := by
  have hp : pre := by by_contra hc; exact hs fun h => absurd h hc
  obtain ⟨t', ht', hq⟩ := h hp
  cases ht'
  exact ⟨hp, hq⟩

/-- What a step that maps no memory below the arena and opens no stream keeps. -/
structure FrameOK (s t : PState) : Prop where
  jobs : t.g.jobs = s.g.jobs
  allocs : t.g.allocs = s.g.allocs
  heap : t.g.heap = s.g.heap
  files : t.g.files = s.g.files
  zone : ∀ x, x < A0 → t.m.memory.permits .read x = true → s.m.memory.permits .read x = true
  streams : ∀ f st, fileR t.m.memory f st → ∃ st0, fileR s.m.memory f st0

theorem inv_of_frame {s t : PState} (hI : Inv s) (h : FrameOK s t) : Inv t := by
  refine ⟨by unfold JobsOK; rw [h.jobs]; exact hI.1, fun hm => ?_⟩
  have hm' : InMain s.g := by obtain ⟨js, hj⟩ := hm; exact ⟨js, by rw [← h.jobs, hj]⟩
  obtain ⟨⟨L, hL, hsz, hcov⟩, ⟨K, hK, hmem⟩⟩ := hI.2 hm'
  refine ⟨⟨L, by rw [h.allocs]; exact hL, fun b hb => by rw [h.heap]; exact hsz b hb,
    fun x hx hr => hcov x hx (h.zone x hx hr)⟩, ⟨K, by rw [h.files]; exact hK, fun f st hf => ?_⟩⟩
  obtain ⟨st0, h0⟩ := h.streams f st hf
  exact hmem f st0 h0

theorem not_arena_low {x : Nat} (hx : x < A0) : ¬ Arena x := fun h => by unfold Arena at h; omega

/-- The frame of a library call (`LibRet`) whose `fp` is readable memory outside the arena. -/
theorem frame_libRet {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult}
    {W : World} {fp : Nat → Prop} {s t : PState}
    (h : LibRet (E0 fs) W fp s t) (hfpR : ∀ x, fp x → x < A0 → s.m.memory.permits .read x = true)
    (hfpA : ∀ x, fp x → ¬ Arena x) :
    (∀ x, x < A0 → t.m.memory.permits .read x = true → s.m.memory.permits .read x = true) ∧
      (∀ f st, fileR t.m.memory f st → ∃ st0, fileR s.m.memory f st0) := by
  obtain ⟨-, -, -, -, -, -, hmap, hnew⟩ := h
  refine ⟨fun x hx hr => ?_, fun f st hf => ?_⟩
  · by_contra hc
    have hs : s.m.memory.permits .read x = false := by simpa using hc
    by_cases hf : fp x
    · exact hc (hfpR x hf hx)
    · have := hmap x hf hs (not_arena_low hx) .read
      rw [this, hs] at hr; exact absurd hr (by simp)
  · rcases hnew f st hf with h | h
    · exact h
    · exfalso
      have hsl := slot_lt hf.1
      have : 0 < S0 := by decide
      exact hfpA f.toNat (h f.toNat ⟨le_refl _, by omega⟩) ⟨by omega, by omega⟩

/-- Same, from the unconditional frame of `framed` (`fp = False`). -/
theorem frame_noMap {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} {s t : PState}
    (hmap : NoMap (E0 fs) (fun _ => False) s t) (hnew : NoNewStream (E0 fs) (fun _ => False) s t) :
    (∀ x, x < A0 → t.m.memory.permits .read x = true → s.m.memory.permits .read x = true) ∧
      (∀ f st, fileR t.m.memory f st → ∃ st0, fileR s.m.memory f st0) := by
  refine ⟨fun x hx hr => ?_, fun f st hf => ?_⟩
  · by_contra hc
    have hs : s.m.memory.permits .read x = false := by simpa using hc
    have := hmap x id hs (not_arena_low hx) .read
    rw [this, hs] at hr; exact absurd hr (by simp)
  · rcases hnew f st hf with h | h
    · exact h
    · exact absurd (h f.toNat ⟨le_refl _, by have := slot_lt hf.1; omega⟩) id

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
