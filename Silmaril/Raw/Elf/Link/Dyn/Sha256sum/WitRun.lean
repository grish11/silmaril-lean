module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitRunPres
public import Silmaril.Raw.Elf.Link.Dyn.Proc.RunInv
public import Silmaril.Raw.Elf.Link.Dyn.Proc.StepFrame

/-! # GNU `sha256sum` witness: an actual run (stdin tier)

The concrete process of `WitLoad`/`WitWorld`, in the world `Wr data`: every import bound to its
contract (the total allocation contracts of `Streams.Defs`), the library entering `main` with
the resource invariant `InvR` and, from the state the start-up produces, with `MainLib`
(`ArS`). For it:

* `inv_step`: every `ok` step from a state of `Inv` that does not stop stays in `Inv`
  (instructions: `StepFrame.open9_step_wframe`; library calls: `entry_inv`; the gate: the job
  queue's shape);
* `progress_inv`: every state of `Inv` has an outcome (`proc_progressP`; `malloc`/`fopen` have
  room by `zone_room`/`slot_room`; `main` is entered with `entM` or a fresh `mainMem`);
* `sha256sum_stdin_runs`: from the kernel's state `s0 [a00]` a run reaches the end with the
  specification's status and output (`Proc.must_run_of_inv` on `sha256sum_stdinK`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.RelIsa (Res RunsInR)
open Silmaril.X86.Ext (loadN)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total
open Silmaril.Elf.Link.Dyn.Imports

/-! ## Steps keep the invariant -/

theorem jobsOK_tail {j : Job} {js : List Job} (h : JobsOK (j :: js)) : JobsOK js := by
  unfold JobsOK at *
  intro hm; exact h (List.mem_of_mem_tail hm)

theorem not_main_of_jobs {g : Ghost} {j : Job} {js : List Job} (hj : g.jobs = j :: js) (h : JobsOK (j :: js))
    (hne : j ≠ .exitRax) : ¬ InMain g := by
  rintro ⟨js', h'⟩; rw [hj] at h'; cases h'; exact hne rfl

theorem exitJobs_ok (W : World) (g : Ghost) (st : Word) : JobsOK (exitJobs W g st) ∧ ¬ InMain { g with jobs := exitJobs W g st } := by
  constructor
  · unfold JobsOK exitJobs
    intro hm
    have := List.mem_of_mem_tail hm
    simp at this
  · rintro ⟨js, hj⟩
    have : Job.exitRax ∈ exitJobs W g st := by simp only at hj; rw [hj]; exact List.mem_cons_self
    unfold exitJobs at this
    simp at this

theorem frame_step {s : PState} {m' : MState} (h : Silmaril.X86.Open9.step s.m = some m') (hI : Inv s) :
    Inv ⟨m', s.g⟩ := by
  have hw := StepFrame.open9_step_wframe h
  have hp : ∀ acc a, m'.memory.permits acc a = s.m.memory.permits acc a := by
    intro acc a; unfold Memory.permits; rw [hw.1]
  refine inv_of_frame hI ⟨rfl, rfl, rfl, rfl, fun x _ hr => by rw [← hp]; exact hr, fun f st hf => ⟨st, ?_⟩⟩
  have hro := hf.2.2.2
  refine ⟨hf.1, hf.2.1, ?_, fun k hk => by rw [← hp]; exact hro k hk⟩
  rw [← hf.2.2.1]
  refine (Keeps.readBytes (P := fun x => f.toNat ≤ x ∧ x < f.toNat + (64 + st.rd.length)) ?_
    (fun k hk => ⟨by omega, by omega⟩)).symm
  intro x hx
  refine ⟨hw.2 x ?_, fun acc => hp acc x⟩
  have h1 : m'.memory.permits .write x = false := by
    have := hro (x - f.toNat) (by omega)
    rwa [show f.toNat + (x - f.toNat) = x by omega] at this
  rwa [hp] at h1

/-- The `main` guarantee of a concrete world: the resource invariant, and `P` at the entries the
start-up produces. -/
def CondS (t : PState) : Prop :=
  Keeps Wf.Kept (s0 [a00]).m.memory t.m.memory ∧ t.m.core.fsBase = fs0 ∧
    t.m.core.read .rsi = sp0 + 8#64 ∧ t.m.core.read .rdi = 1#64

def ArS (data : List Byte) (t : PState) : Prop := InvR t ∧ (CondS t → Astdin fsE data t)

theorem fns0_fn {p : Word × Fn} (h : p ∈ fns0) : p.2 = .libcStartMain ∨ p.2 = .cxaFinalize ∨ ∃ n, p.2 = .named n := by
  simp only [fns0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | (left; rfl) | (right; left; rfl) | (right; right; exact ⟨_, rfl⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Every `ok` step from a state of the invariant that does not stop stays in it.** -/
theorem inv_step (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (A : PState → Prop) (hA : ∀ t, A t → InvR t) {s t : PState} (hI : Inv s)
    (hns : ¬ (proc (Wof fs A)).step s .stop) (h : (proc (Wof fs A)).step s (.ok t)) : Inv t := by
  simp only [proc] at h hns
  unfold step at h hns
  cases hd : s.g.done with
  | some _ => simp [hd] at h
  | none =>
    simp only [hd] at h hns
    by_cases hin : (Wof fs A).InImage s.m.core.rip.toNat
    · simp only [hin, ↓reduceIte] at h hns
      cases hst : Silmaril.X86.Open9.step s.m with
      | none => simp [hst] at h
      | some m' =>
        simp only [hst, Res.ok.injEq] at h
        subst h
        exact frame_step hst hI
    · simp only [hin, ↓reduceIte] at h hns
      unfold extStep at h hns
      by_cases hg : s.m.core.rip = (Wof fs A).gate
      · simp only [hg, ↓reduceIte] at h hns
        unfold gateStep at h hns
        have hJ := hI.1
        cases hj : s.g.jobs with
        | nil => simp [hj] at hns
        | cons j js =>
          rw [hj] at hJ
          simp only [hj] at h hns
          cases j with
          | call f a1 a2 a3 =>
            obtain ⟨-, -, -, -, -, hgt⟩ := contract_post h hns
            refine inv_jobs (by rw [hgt]; exact jobsOK_tail hJ) ?_
            rintro ⟨js', h'⟩; rw [hgt] at h'; simp only at h'; subst h'
            exact hJ List.mem_cons_self
          | call0 f =>
            obtain ⟨-, -, hgt, -, -⟩ := contract_post h hns
            refine inv_jobs (by rw [hgt]; exact jobsOK_tail hJ) ?_
            rintro ⟨js', h'⟩; rw [hgt] at h'; simp only at h'; subst h'
            exact hJ List.mem_cons_self
          | main f a1 a2 a3 =>
            obtain ⟨-, -, -, -, -, hgt, hat⟩ := contract_post h hns
            exact ⟨by rw [hgt]; exact hJ, hA t hat⟩
          | exitRax =>
            obtain ⟨-, _, -, -, hgt, -⟩ := contract_post h hns
            exact inv_jobs (by rw [hgt]; exact jobs_exit _) (not_main_exit (by rw [hgt]))
          | exit st =>
            obtain ⟨-, -, hgt, -⟩ := contract_post h hns
            have := exitJobs_ok (Wof fs A) s.g st
            refine inv_jobs (by rw [hgt]; exact this.1) (by rw [hgt]; exact this.2)
          | halt st =>
            obtain ⟨-, w, -, -, hgt⟩ := contract_post h hns
            refine inv_jobs (by rw [hgt]; simp [JobsOK]) ?_
            rintro ⟨js', h'⟩; rw [hgt] at h'; cases h'
      · simp only [hg, ↓reduceIte] at h hns
        simp only [show (Wof fs A).lazy = none from rfl] at h hns
        cases hf : (Wof fs A).fns.find? (·.1 == s.m.core.rip) with
        | none => simp [hf] at h
        | some p =>
          simp only [hf] at h hns
          have hmem : p ∈ fns0 := List.mem_of_find?_eq_some hf
          rcases fns0_fn hmem with hp | hp | ⟨n, hp⟩
          · rw [hp] at h hns
            obtain ⟨-, -, hgt⟩ := contract_post h hns
            refine inv_jobs ?_ ?_
            · rw [hgt]; simp [JobsOK, Wof, Wf]
            · rintro ⟨js', h'⟩; rw [hgt] at h'; simp [Wof, Wf] at h'
          · rw [hp] at h hns
            obtain ⟨-, -, hgt, hmt⟩ := contract_post h hns
            exact inv_of_frame hI ⟨by rw [hgt], by rw [hgt], by rw [hgt], by rw [hgt],
              fun x _ hr => by rw [← hmt]; exact hr, fun f st hf => ⟨st, by rw [← hmt]; exact hf⟩⟩
          · rw [hp] at h hns
            simp only [fnStep, Wof] at h hns
            unfold Witness.namedOf at h hns
            cases he : (table0 fs).find? (·.1 == n) with
            | none => simp [he] at h
            | some e =>
              simp only [he] at h hns
              exact entry_inv (List.mem_of_find?_eq_some he) hI h hns


/-! ## Every state of the invariant has an outcome -/

theorem kept_low {x : Nat} (hx : x < A0) : ¬ Wf.Kept x := by
  intro h; rw [kept_iff] at h; unfold A0 at hx; omega

theorem wf_arena (a : Nat) (h : Wf.Kept a) : ¬ Arena a := kept_arena fsE (fun _ => True) a h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **Every contract of the concrete table has an outcome at a state of the invariant.** -/
theorem entry_total (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (hfs : ∀ p e, fs p ≠ .openErr e)
    {e : Name × (PState → Res PState → Prop)} (he : e ∈ table0 fs) {s : PState} (hI : Inv s) : ∃ r, e.2 s r := by
  simp only [table0, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact strrchr_ok fs _ Wf s
  · exact framed_quiet fs (lb0 + 0x204248#64) Wf s (fun _ _ => False)
  · exact framed_quiet fs (lb0 + 0x204248#64) Wf s (fun _ _ => False)
  · exact framed_quiet fs (lb0 + 0x204248#64) Wf s (fun _ _ => False)
  · exact framed_same fs (lb0 + 0x204248#64) Wf s (fun _ _ => False) (cxaAtexitFirst Wf) 0#64
      { s.g with atexit := s.g.atexit ++ [s.m.core.read .rdi] }
      fun _ => ⟨_, rfl, retState_returns Wf s _ _, by rw [retM_rax]; rfl, rfl⟩
  · exact setvbuf_ok fs _ Wf s
  · exact getopt_ok fs _ Wf s
  · exact clearerr_ok fs _ Wf s wf_arena
  · exact lseek_ok fs _ Wf s
  · exact fopen_total fs _ Wf s wf_arena hfs
      (fun st hR => slot_room (hI.2 hR.1).2 hR.2.2.1)
  · exact fadvise_ok fs _ Wf s
  · exact malloc_total fs _ Wf s fun hR => zone_room (hI.2 hR.1).1 hR.2.2.1 hR.2.2.2 fun x hx => kept_low hx
  · exact free_ok fs _ Wf s
  · exact freadChk_ok fs _ Wf s wf_arena
  · exact framed_init fs _ Wf s
  · exact framed_update fs _ Wf s
  · exact framed_final fs _ Wf s
  · exact fileno_ok fs _ Wf s
  · exact freading_ok fs _ Wf s
  · exact fflush_ok fs _ Wf s
  · exact fclose_ok fs _ Wf s
  · exact fpending_ok fs _ Wf s
  · exact printfHex_ok fs _ Wf s
  · exact overflow_ok fs _ Wf s
  · exact fputs_ok fs _ Wf s
  · exact strcspn_ok fs _ Wf s

theorem named_total (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (hfs : ∀ p e, fs p ≠ .openErr e) (A : PState → Prop) (n : Name) (s : PState) (hI : Inv s) :
    ∃ r, (Wof fs A).named n s r := by
  show ∃ r, Witness.namedOf (table0 fs) n s r
  unfold Witness.namedOf
  cases hf : (table0 fs).find? (·.1 == n) with
  | none => exact ⟨.stop, rfl⟩
  | some e => exact entry_total fs hfs (List.mem_of_find?_eq_some hf) hI

/-- Exit callbacks are entered on the fresh stack, every stream kept. -/
theorem call0_total (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (A : PState → Prop) (s : PState) (f : Word) (g : Ghost) :
    ∃ t, Enters (Wof fs A) s t f ∧ t.g = g ∧ (Wof fs A).atCall t ∧ (Wof fs A).atGate s t := by
  refine ⟨⟨⟨coreE f 0 0 0 s.m.core.fsBase, callMem s.m.memory⟩, g⟩,
    enters_of (fun a => Iff.rfl) rfl s f 0 0 0 g _ _ (callMem_kept (fun a => Iff.rfl) s.m.memory), rfl, ?_,
    fun f' st h => fileR_keep_slot h fun x h1 h2 => ?_⟩
  · show A0 + K0 * S0 + 1024 ≤ ((coreE f 0 0 0 s.m.core.fsBase).read .rsp).toNat
    rw [coreE_rsp, rspT_toNat]; decide
  · have hsl := slot_lt h.1
    have := callMem_keep s.m.memory x (by simp only [InStk2, stk2Lo]; unfold A0 K0 S0 at hsl; unfold S0 at h2; omega)
    exact ⟨this.1, this.2⟩

/-- `main` is entered: from the state the start-up produces with `MainLib` (`entM`), otherwise on
a fresh `mainMem`. -/
theorem main_total (data : List Byte) (hd : 64 + data.length ≤ S0) (s : PState) (f a1 a2 a3 : Word)
    (g : Ghost) : ∃ t, Enters (Wof fsE (ArS data)) s t f ∧ t.m.core.read .rdi = a1 ∧
      t.m.core.read .rsi = a2 ∧ t.m.core.read .rdx = a3 ∧ t.g = g ∧ (Wof fsE (ArS data)).atMain t := by
  by_cases hc : Keeps Wf.Kept (s0 [a00]).m.memory s.m.memory ∧ s.m.core.fsBase = fs0 ∧ a1 = 1#64 ∧
      a2 = sp0 + 8#64
  · obtain ⟨hk, hfs, rfl, rfl⟩ := hc
    exact ⟨entM data f a3 g, enters_entM data hd s f a3 g hk hfs, coreM_rdi f a3, coreM_rsi f a3,
      coreM_rdx f a3, rfl, invR_entM data f a3 g,
      fun _ => ⟨Cm fsE, inF, sp0 + 64#64, guard0, mainLib_entM fsE data hd f a3 g⟩⟩
  · refine ⟨⟨⟨coreE f a1 a2 a3 s.m.core.fsBase, mainMem s.m.memory⟩, g⟩,
      enters_of (fun a => Iff.rfl) rfl s f a1 a2 a3 g _ _ (mainMem_kept (fun a => Iff.rfl) s.m.memory),
      coreE_rdi _ _ _ _ _, coreE_rsi _ _ _ _ _, coreE_rdx _ _ _ _ _, rfl, invR_mainMem s _ g, fun hC => ?_⟩
    exfalso
    obtain ⟨hk, hfs, hrsi, hrdi⟩ := hC
    exact hc ⟨hk.trans (Keeps.symm' (mainMem_kept (W := Wf) (fun a => Iff.rfl) s.m.memory)), hfs,
      by rw [← coreE_rdi f a1 a2 a3 s.m.core.fsBase]; exact hrdi,
      by rw [← coreE_rsi f a1 a2 a3 s.m.core.fsBase]; exact hrsi⟩

/-- The concrete stdin-tier world. -/
def Wr (data : List Byte) : World := Wof fsE (ArS data)

theorem progress_inv (data : List Byte) (hd : 64 + data.length ≤ S0) :
    ∀ s, Inv s → ∃ r, (proc (Wr data)).step s r :=
  proc_progressP (Wr data) Inv (by show b0.toNat + 0xa188 ≤ 2 ^ 62; rw [b0_toNat]; decide)
    (fun a h => by
      rcases h with h | h <;> simp only [Wr, Wof, Wf, args0, tls0, sp0_toNat, fs0_toNat, lb0_toNat] at h <;> omega)
    (fun res slots h => by cases h)
    (fun n s hI => named_total fsE (fun p e h => by cases h) _ n s hI)
    (fun s f a1 a2 a3 g _ => main_total data hd s f a1 a2 a3 g)
    (fun s f g _ => call0_total fsE _ s f g)
    (fun s g f st h => h)

theorem inv_s0 (args : List (List Byte)) : Inv (s0 args) :=
  ⟨by simp [JobsOK, s0], fun h => by obtain ⟨js, hj⟩ := h; simp [s0] at hj⟩

/-! ## The run -/

/-- `sha256sum_stdinK` for the concrete world `Wr data`. -/
theorem sha_stdin_must (data : List Byte) (posix : Bool)
    (fs' : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) :
    MustQ (Wr data) (Ended (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).status fun w =>
      w = (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).stdout.map UInt8.toBitVec ∧
      (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).stderr = []) (s0 [a00]) :=
  sha256sum_stdinK hFk hFc hFl (rfl : ifn0 (lb0 + 0xb5210#64) = some sr0) (rfl : ifn0 (lb0 + 0xb4410#64) = some sc0)
    (mainImps0 fsE _) (tailImps0 fsE _) (exitOk0 fsE _) (loadedW _) (start0 fsE _ [a00] hargc1)
    (by show 1 ≤ mAllocs ∧ 0x8048 ≤ mHeap; decide)
    (fun t hat hk hfs hrsi hrdi => by
      obtain ⟨C, fi, a0p, g, h⟩ := hat.2 ⟨hk, hfs, hrsi, by rw [hrdi]; decide⟩
      exact ⟨C, fi, a0p, g, mainLib_tr h⟩) posix fs'

/-- **GNU `sha256sum` reading standard input runs to completion** (stdin tier).

For the concrete loaded process (`s0 [a00]`: `sha256sum` loaded with `libcrypto.so.3`, `libc.so.6`
and `ld.so` holding the pinned chunks, `argv = ["sha256sum"]`) in the concrete world `Wr data`
(every import bound to its contract, the slot stream representation, resource bounds
`mAllocs = 4` requests of `mHeap = 64 KiB`), a run exists from the kernel's state and ends with the
status and standard output of silmaril's specification `Silmaril.Apps.Sha256sum.sha256sum`.

Model limit (not a property of `sha256sum`): the concrete stream representation holds standard
input in one 1 MiB slot, so `64 + data.length ≤ S0`.

Trusted base: the x86 semantics `Silmaril.X86.Open9` and the process model `Proc.proc`; the loader
relation `ExeLoaded` and the pinned library chunks; the import contracts of `Streams.Defs`,
`Imports.Defs` and `Proc.Defs` (what glibc and libcrypto are assumed to do), the stream
representation `slotRep` and the concrete `Env`/`World` of `WitWorld`; silmaril's specification
`Silmaril.Apps.Sha256sum.sha256sum`. -/
theorem sha256sum_stdin_runs_spec (data : List Byte) (hd : 64 + data.length ≤ S0) (posix : Bool)
    (fs' : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) :
    ∃ t, RunsInR (proc (Wr data)) (fun _ => True) (s0 [a00]) t ∧
      Ended (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).status (fun w =>
        w = (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).stdout.map UInt8.toBitVec ∧
        (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).stderr = []) t :=
  must_run_of_inv Inv trivial (sha_stdin_must data posix fs') (inv_s0 _) (progress_inv data hd)
    (fun _ _ hI hs h => inv_step fsE (ArS data) (fun _ h => h.1) hI hs h)

/-- **GNU `sha256sum` on standard input: a run ends with status 0 and standard output
`hex(SHA-256(data)) ++ "  -\n"`** (`stdinLine data`). Same model, limit and trusted base as
`sha256sum_stdin_runs_spec`. -/
theorem sha256sum_stdin_runs (data : List Byte) (hd : 64 + data.length ≤ S0) :
    ∃ t, RunsInR (proc (Wr data)) (fun _ => True) (s0 [a00]) t ∧ Ended 0 (fun w => w = stdinLine data) t := by
  obtain ⟨t, hr, hE⟩ := sha256sum_stdin_runs_spec data hd false fsE
  refine ⟨t, hr, ?_⟩
  have hspec := Silmaril.Apps.Sha256sum.Sys.sha256sum_stdin (toSpec a00) false fsE (toSpec data)
  simp only [stdinWorld, hspec] at hE
  obtain ⟨w, hdone, hw, -⟩ := hE
  exact ⟨w, hdone, by rw [hw, ← stdinLine_spec]⟩

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
