module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitWorld
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiRun

/-! # GNU `sha256sum`: the hypotheses of the loader-level theorems are jointly satisfiable

For the concrete process of `WitLoad`/`WitWorld` (kernel stack with `argv = ["sha256sum"]`, resp.
`["sha256sum", "f"]`), every hypothesis of `StdinRun.sha256sum_stdinK` (stdin tier) and of
`MultiLoaded.sha256sum_files` (file tier) holds: `sha_stdin_hyps`, `sha_files_hyps`, and the
theorems' conclusions for it, `sha_stdin_s0`, `sha_files_s0`.

That a run exists is shown separately: `WitRun.sha256sum_stdin_runs` and
`WitRunF.sha256sum_files_runs`, in the worlds `Wr`/`Wfl` whose `main` guarantee also carries the
resource invariant (`malloc`/`fopen` are total contracts: NULL without room, `Streams.Defs`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.RelIsa (Res)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Proc.Witness
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total
open Silmaril.Elf.Link.Dyn.Imports

/-! ## Reading a page -/

theorem read_page {mem : Memory} {base o n : Nat} {page : List Byte}
    (hget : ∀ j, j < page.length → mem.bytes.get? (base + j) = page[j]?)
    (hperm : ∀ j, j < n → mem.permits .read (base + o + j) = true)
    (hon : o + n ≤ page.length) (hlim : base + o + n < 2 ^ 64) :
    mem.readBytes (base + o) n = some ((page.drop o).take n) := by
  have hn : ((page.drop o).take n).length = n := by simp; omega
  have := readWith_of_points (mem := mem) (acc := .read) (l := (page.drop o).take n) (a := base + o)
    (by rw [hn]; omega) (by omega)
    (fun k hk => ⟨hperm k (by rw [hn] at hk; exact hk), by
      rw [show base + o + k = base + (o + k) by omega, hget _ (by rw [hn] at hk; omega)]
      simp [List.getElem?_eq_getElem (show o + k < page.length by rw [hn] at hk; omega)]⟩)
  rw [hn] at this
  simpa [Memory.readBytes] using this

/-! ## The kernel's stack -/

/-- The argument strings live from `sp0 + 64`. -/
def argBase : Nat := 4096 + 64

/-- The kernel's stack pages for `argv = a0 :: as` (each string NUL-terminated, in order): `argc`
at `sp0`, the pointers, `NULL`, an empty environment (`NULL`). -/
def stkOf (args : List (List Byte)) : List Byte :=
  let offs := (args.map (·.length + 1)).scanl (· + ·) 0
  pageOf 8192 ([(4096, Silmaril.X86.Ext.leBytes (BitVec.ofNat 64 args.length) 8)] ++
    (List.range args.length).map (fun i => (4104 + 8 * i,
      Silmaril.X86.Ext.leBytes (sp0 + BitVec.ofNat 64 (64 + offs.getD i 0)) 8)) ++
    [(argBase, (args.map (· ++ [0#8])).flatten)])

theorem stkOf_length (args : List (List Byte)) : (stkOf args).length = 8192 := pageOf_length _ _

theorem memW_stk (stk : List Byte) {j : Nat} (hj : j < stk.length) :
    (memW stk).bytes.get? (stackLo + j) = stk[j]? := by
  unfold memW
  dsimp only
  rw [Memory.install_outside _ _ _ _ (Or.inr (Nat.le_trans (by rw [tlsPage_length]; decide) (Nat.le_add_right _ _)))]
  rw [Memory.install_outside _ _ _ _ (Or.inr (Nat.le_trans (by rw [libPage_length]; decide) (Nat.le_add_right _ _)))]
  rw [Memory.install_get _ _ _ _ hj, List.getElem?_eq_getElem hj]

theorem stack_permits {acc : Access} (stk : List Byte) (hacc : acc = .read ∨ acc = .write) {a : Nat}
    (h1 : stackLo ≤ a) (h2 : a < stackLo + 8192) : (memW stk).permits acc a = true := by
  unfold Memory.permits
  rw [List.any_eq_true]
  refine ⟨⟨stackLo, 8192, perm true true false⟩, by simp [memW, regions0], ?_⟩
  have e : stackLo = 0x7ffffffdd000 := by decide
  rw [e] at h1 h2
  rcases hacc with rfl | rfl <;> simp [Region.Contains, perm, Permissions.allows, e] <;> omega

/-- The initial state: `_start`, `rsp = sp0`, `fsBase = fs0`. -/
def core0 : State :=
  ⟨fun r => if r = .rsp then sp0 else 0, b0 + 0x3a40#64, ⟨none, none, none, none, none, none⟩, fs0⟩

def s0 (args : List (List Byte)) : PState :=
  ⟨⟨core0, memW (stkOf args)⟩, { jobs := [], out := [], atexit := [], done := none }⟩

set_option maxRecDepth 100000 in
theorem start0 (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (A : PState → Prop) (args : List (List Byte))
    (hargc : ((stkOf args).drop 4096).take 8 = Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 args.length]) :
    ShaStartState (Wof fs A) b0 (s0 args) (BitVec.ofNat 64 args.length) := by
  have hsp : core0.read .rsp = sp0 := rfl
  refine ⟨rfl, by show (core0.read .rsp).toNat % 16 = 0; rw [hsp, sp0_toNat], ?_, ?_, rfl⟩
  · refine ⟨by show 4096 ≤ (core0.read .rsp).toNat; rw [hsp, sp0_toNat]; decide,
      by show (core0.read .rsp).toNat + 8 < 2 ^ 64; rw [hsp, sp0_toNat]; decide, fun a h1 h2 => ?_⟩
    change sp0.toNat - 4096 ≤ a at h1
    change a < sp0.toNat + 8 at h2
    have e : stackLo = 0x7ffffffdd000 := by decide
    rw [sp0_toNat] at h1 h2
    have h3 : stackLo ≤ a := by rw [e]; omega
    have h4 : a < stackLo + 8192 := by rw [e]; omega
    refine ⟨stack_permits _ (Or.inl rfl) h3 h4, stack_permits _ (Or.inr rfl) h3 h4, ?_⟩
    rw [wof_kept]
    simp only [ShaImg, args0, tls0, b0_toNat, sp0_toNat, fs0_toNat, lb0_toNat]
    omega
  · show (memW (stkOf args)).readBytes (core0.read .rsp).toNat 8 = _
    rw [hsp, show sp0.toNat = stackLo + 4096 by decide]
    have e : stackLo = 0x7ffffffdd000 := by decide
    rw [read_page (page := stkOf args) (fun j hj => memW_stk _ hj)
      (fun j hj => stack_permits _ (Or.inl rfl) (by omega) (by rw [e]; omega))
      (by rw [stkOf_length]; decide) (by rw [e]; omega), hargc]

/-! ## The stdin tier -/

/-- `"sha256sum"`. -/
def a00 : List Byte := [0x73, 0x68, 0x61, 0x32, 0x35, 0x36, 0x73, 0x75, 0x6d]

/-- The library's guarantee at `main` on the stdin tier. -/
def Astdin (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (data : List Byte)
    (t : PState) : Prop :=
  ∃ C fi a0p g, MainLib (E0 fs) Wf b0 lb0 C fi t a0p a00 data g

theorem mainLib_tr {fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult} {A : PState → Prop}
    {C : Nat → Prop} {fi : Word} {t : PState} {a0p : Word} {a0 data : List Byte} {g : Word}
    (h : MainLib (E0 fs) Wf b0 lb0 C fi t a0p a0 data g) : MainLib (E0 fs) (Wof fs A) b0 lb0 C fi t a0p a0 data g :=
  ⟨h.lo, ⟨h.env.out, h.env.err, h.env.inp, ⟨h.env.vars.out, h.env.vars.err, h.env.vars.kept, h.env.vars.bound⟩,
    h.env.np, h.env.wr⟩, h.hC, h.pinC, h.pinK, h.optC, h.optK, h.optL, h.opt, h.lbB, h.imgVar, h.argsImg, h.argc,
    h.argv, h.argv0, h.argv0k, h.a0s, h.a0k, h.a0nz, h.noSlash, h.guard, h.guardk, h.guardImg, h.var, h.vark,
    h.varImg, h.fi0, h.fiO, h.fiE, h.avHi, h.av, h.avA, h.avR, h.avW, h.avVar, h.avIn, h.avG⟩

theorem hargc1 : ((stkOf [a00]).drop 4096).take 8 = Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 [a00].length] := by
  decide +kernel

/-- **Every hypothesis of `sha256sum_stdinK` holds** for the concrete process (any file system `fs`,
any standard input `data`). -/
theorem sha_stdin_hyps (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (data : List Byte) :
    let W := Wof fs (Astdin fs data)
    ChunksOf Fk0 cryptoChunks ∧ ChunksOf Fc0 libcChunks ∧ ChunksOf Fl0 ldChunks ∧
    ifn0 (lb0 + 0xb5210#64) = some sr0 ∧ ifn0 (lb0 + 0xb4410#64) = some sc0 ∧
    MainImps (E0 fs) W b0 lb0 sr0 ∧ TailImps (E0 fs) shaRep W b0 lb0 kb0 sc0 ∧ ExitOk (E0 fs) W b0 lb0 ∧
    ExeLoaded [shaFile, Fk0, Fc0, Fl0] [b0, kb0, lb0, ldb0] ifn0 false res0 (s0 [a00]).m.memory ∧
    ShaStartState W b0 (s0 [a00]) 1#64 ∧
    (∀ t, W.atMain t → Keeps W.Kept (s0 [a00]).m.memory t.m.memory → t.m.core.fsBase = (s0 [a00]).m.core.fsBase →
      t.m.core.read .rsi = (s0 [a00]).m.core.read .rsp + 8#64 →
      t.m.core.read .rdi = ((1#64 : Word).setWidth 32).setWidth 64 →
      ∃ C fi a0p g, MainLib (E0 fs) W b0 lb0 C fi t a0p a00 data g) :=
  ⟨hFk, hFc, hFl, rfl, rfl, mainImps0 fs _, tailImps0 fs _, exitOk0 fs _, loadedW _,
    start0 fs _ [a00] hargc1, fun _ ⟨C, fi, a0p, g, h⟩ _ _ _ _ => ⟨C, fi, a0p, g, mainLib_tr h⟩⟩

/-- `sha256sum_stdinK` for the concrete process. -/
theorem sha_stdin_s0 (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) (data : List Byte)
    (posix : Bool) (fs' : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult) :
    MustQ (Wof fs (Astdin fs data))
      (Ended (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).status fun w =>
        w = (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).stdout.map UInt8.toBitVec ∧
        (Silmaril.Apps.Sha256sum.sha256sum (stdinWorld a00 data posix fs')).stderr = []) (s0 [a00]) := by
  obtain ⟨hk, hc, hl, hsr, hsc, I, T, XO, hload, hs, hA⟩ := sha_stdin_hyps fs data
  exact sha256sum_stdinK hk hc hl hsr hsc I T XO hload hs (by show 1 ≤ mAllocs ∧ 0x8048 ≤ mHeap; decide) hA posix fs'

/-! ## The file tier: `sha256sum f` -/

/-- `"f"`. -/
def f00 : List Byte := [0x66]

/-- A file system where every file opens and is empty. -/
def fsE : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult := fun _ => .ok []

/-- The library's guarantee at `main` on the file tier (`argv = ["sha256sum", "f"]`). -/
def Afiles (t : PState) : Prop :=
  ∃ C fi sti a0p g ops, ops.map Prod.snd = [f00] ∧ MainLibF (E0 fsE) Wf b0 lb0 C fi sti t a0p a00 ops g

theorem argsAt_tr {A : PState → Prop} {m : Memory} :
    ∀ {q : Word} {ops : List (Word × List Byte)}, ArgsAt Wf m q ops → ArgsAt (Wof fsE A) m q ops
  | _, [], _ => trivial
  | _, (_, _) :: _, ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, argsAt_tr h5⟩

theorem mainLibF_tr {A : PState → Prop} {C : Nat → Prop} {fi : Word} {sti : St} {t : PState} {a0p : Word}
    {a0 : List Byte} {ops : List (Word × List Byte)} {g : Word}
    (h : MainLibF (E0 fsE) Wf b0 lb0 C fi sti t a0p a0 ops g) :
    MainLibF (E0 fsE) (Wof fsE A) b0 lb0 C fi sti t a0p a0 ops g :=
  ⟨h.lo, ⟨h.env.out, h.env.err, h.env.inp, ⟨h.env.vars.out, h.env.vars.err, h.env.vars.kept, h.env.vars.bound⟩,
    h.env.np, h.env.wr⟩, h.hC, h.pinC, h.pinK, h.optC, h.optK, h.optL, h.opt, h.lbB, h.imgVar, h.argsImg,
    h.argv, h.argv0, h.argv0k, h.a0s, h.a0k, h.a0nz, h.noSlash, h.guard, h.guardk, h.guardImg,
    argsAt_tr h.args, h.ne, h.argc, h.argcLim, h.avLim⟩

theorem multiImps0 (A : PState → Prop) : MultiImps (E0 fsE) shaRep (Wof fsE A) b0 lb0 kb0 sc0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    slot_tailLaws (E0 fsE) rfl (slot0 fsE) out_ne0 (Wof fsE A) (kept_arena fsE A)
  exact ⟨digImps0 fsE A, printImps0 fsE A, h1, h2, h3, h4, h5, rfl, h6⟩

theorem hargc2 : ((stkOf [a00, f00]).drop 4096).take 8 =
    Silmaril.Machine.LittleEndian.encodeWords [BitVec.ofNat 64 [a00, f00].length] := by
  decide +kernel

theorem opOk_f : OpOk (E0 fsE) (fun _ => []) f00 := ⟨by decide, by decide, rfl, Nat.zero_le _⟩

/-- **Every hypothesis of `sha256sum_filesK` holds** for the concrete process running
`sha256sum f` (a file system where `f` opens and is empty). -/
theorem sha_files_hyps :
    let W := Wof fsE Afiles
    ChunksOf Fk0 cryptoChunks ∧ ChunksOf Fc0 libcChunks ∧ ChunksOf Fl0 ldChunks ∧
    ifn0 (lb0 + 0xb5210#64) = some sr0 ∧ ifn0 (lb0 + 0xb4410#64) = some sc0 ∧
    MainImps (E0 fsE) W b0 lb0 sr0 ∧ MultiImps (E0 fsE) shaRep W b0 lb0 kb0 sc0 ∧
    (E0 fsE).optindA = lb0 + 0x204248#64 ∧ ExitOk (E0 fsE) W b0 lb0 ∧
    ExeLoaded [shaFile, Fk0, Fc0, Fl0] [b0, kb0, lb0, ldb0] ifn0 false res0 (s0 [a00, f00]).m.memory ∧
    ShaStartState W b0 (s0 [a00, f00]) 2#64 ∧
    (∀ t, W.atMain t → Keeps W.Kept (s0 [a00, f00]).m.memory t.m.memory →
      t.m.core.fsBase = (s0 [a00, f00]).m.core.fsBase →
      t.m.core.read .rsi = (s0 [a00, f00]).m.core.read .rsp + 8#64 →
      t.m.core.read .rdi = ((2#64 : Word).setWidth 32).setWidth 64 →
      ∃ C fi sti a0p g ops, ops.map Prod.snd = [f00] ∧ MainLibF (E0 fsE) W b0 lb0 C fi sti t a0p a00 ops g) ∧
    (∀ n ∈ [f00], OpOk (E0 fsE) (fun _ => []) n) ∧ (∀ n ∈ [f00], n ≠ []) :=
  ⟨hFk, hFc, hFl, rfl, rfl, mainImps0 fsE _, multiImps0 _, rfl, exitOk0 fsE _, loadedW _,
    start0 fsE _ [a00, f00] hargc2,
    fun _ ⟨C, fi, sti, a0p, g, ops, hn, h⟩ _ _ _ _ => ⟨C, fi, sti, a0p, g, ops, hn, mainLibF_tr h⟩,
    by simp [opOk_f], by simp [f00]⟩

/-- `sha256sum_filesK` for the concrete process. -/
theorem sha_files_s0 (posix : Bool) (stdin : Silmaril.Apps.Sha256sum.Stdin) :
    MustQ (Wof fsE Afiles)
      (Ended (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 fsE).fs stdin)).status fun w =>
        w = (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 fsE).fs stdin)).stdout.map UInt8.toBitVec ∧
        (Silmaril.Apps.Sha256sum.sha256sum (filesWorldN a00 [f00] posix (E0 fsE).fs stdin)).stderr = [])
      (s0 [a00, f00]) := by
  obtain ⟨hk, hc, hl, hsr, hsc, I, M, hopA, XO, hload, hs, hA, hops, hne⟩ := sha_files_hyps
  exact sha256sum_filesK hk hc hl hsr hsc I M hopA XO hload hs (names := [f00])
    (by show 1 ≤ mAllocs ∧ 0x8048 * 1 ≤ mHeap ∧ 1 ≤ mOpen; decide) hA hops hne posix stdin

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
