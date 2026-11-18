module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MultiPre
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinMain

/-! # GNU `sha256sum FILE1 … FILEn`, success tier: `main` to the end of the process

`sha_main_multi`: from `main`'s entry with `argv = a0 :: names` (`n ≥ 1` operands, each a
readable file whose name is printed verbatim: `OpOk`), every run ends with status 0 having
written the operands' lines in order (`linesM`). Composed of `sha_main_head`, `sha_main_buf`,
`sha_main_getopt` (to `0x29fd`), `multi_pre` (to the first `digest_file`), `multi_loop` (the
operands, `main`'s return) and `task_exitPath` (the end of the process).

`sha_main_multi_spec`: the same against the specification `Silmaril.Apps.Sha256sum.sha256sum`
on `filesWorld a0 ops posix E.fs stdin` (`FilesSpec.sha256sum_multi`, `fileLineM_spec`): the
exit status and standard output are the specification's, its standard error is empty.

The restriction on names (`OpOk`): not empty, not starting with `-`, no backslash, LF or CR.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)
open Silmaril.X86.FnContract (AbiEntry AbiReturn)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports

/-- **`main`'s entry on the file tier**: the System V entry, the image, the library state
(`stdout`, `stderr` fresh, `stdin` = `fi` in any state), `argv = a0 :: names` with `a0` free of
`/`, and the layout (as `MainEntryS`, without `argc = 1`). -/
structure MainEntryF (E : Env) (W : World) (b lb kb sr sc : Word) (C : Nat → Prop) (fi : Word) (sti : St)
    (s : PState) (a0p : Word) (a0 : List Byte) (names : List (List Byte)) (g : Word) : Prop where
  rip : s.m.core.rip = b + 0x2750#64
  abi : AbiEntry s.m.core s.m.memory
  room : Room W s.m.memory (s.m.core.read .rsp) 4096
  ghost : s.g.done = none ∧ s.g.atexit = [] ∧ s.g.out = [] ∧ s.g.jobs = [.exitRax]
  mem : ShaMemAll b lb kb sr sc s.m.memory
  rw : ShaRw b s.m.memory
  lo : E.S.lo + 4096 ≤ (s.m.core.read .rsp).toNat
  env : MEnv E W b lb C fi (outSt 1) (outSt 2) sti s.m.memory
  hC : ∀ a, C a → a < (s.m.core.read .rsp).toNat - 4096 ∨ (s.m.core.read .rsp).toNat + 8 ≤ a
  pinC : ∀ a, PinR lb a → C a
  pinK : ∀ a, PinR lb a → ¬ W.Kept a
  optC : ∀ a, OptR E a → C a
  optK : ∀ a, OptR E a → ¬ W.Kept a
  optL : ∀ a, OptR E a → a + 48 < (s.m.core.read .rsp).toNat
  opt : E.optindA.toNat + 4 < 2 ^ 64
  lbB : lb.toNat + 0x2056b0 < 2 ^ 64
  imgVar : ∀ a, ShaImg b a → ¬ VarR lb a
  argsImg : ∀ a, W.args a → ¬ ShaImg b a
  argv : ∀ m, Keeps W.args s.m.memory m → Argv m (s.m.core.read .rsi) (a0 :: names)
  argv0 : loadN s.m.memory (s.m.core.read .rsi) 8 = some a0p
  argv0k : ∀ k, k < 8 → W.Kept ((s.m.core.read .rsi).toNat + k)
  a0s : CStr s.m.memory a0p a0
  a0k : ∀ j, j < a0.length + 1 → W.Kept (a0p.toNat + j)
  a0nz : a0p ≠ 0#64
  noSlash : ∀ x ∈ a0, x ≠ 0x2f#8
  guard : loadN s.m.memory (s.m.core.fsBase + 0x28#64) 8 = some g
  guardk : ∀ j, j < 8 → W.Kept ((s.m.core.fsBase + 0x28#64).toNat + j)
  /-- the library's resources for every operand -/
  res : RoomN E s.g names.length

set_option maxRecDepth 100000 in
/-- **sha256sum FILE1 … FILEn, from `main`'s entry** (no open goal): every run ends with status 0
having written `linesM dat ops`. -/
theorem sha_main_multi {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word} (I : MainImps E W b lb sr)
    (M : MultiImps E R W b lb kb sc) (hopA : E.optindA = lb + 0x204248#64) (XO : ExitOk E W b lb)
    {C : Nat → Prop} {fi : Word} {sti : St} {s : PState} {a0p : Word} {a0 : List Byte}
    {ops : List (Word × List Byte)} {g : Word}
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    (h : MainEntryF E W b lb kb sr sc C fi sti s a0p a0 (ops.map Prod.snd) g) (ht : FilesEntry E W b lb s ops g)
    (hops : ∀ pn ∈ ops, OpOk E dat pn.2) :
    MustQ W (Ended 0 fun w => w = linesM dat ops) s := by
  have hal := h.abi.aligned
  obtain ⟨hd, hat, hout, hjobs⟩ := h.ghost
  obtain ⟨p, n, rest, rfl⟩ : ∃ p n rest, ops = (p, n) :: rest := by
    rcases hops' : ops with _ | ⟨⟨p, n⟩, rest⟩
    · exact absurd hops' ht.ne
    · exact ⟨p, n, rest, rfl⟩
  refine sha_main_head I.img I.hb I.lz I.strrchr I.loc (privKeep E) h.rip h.abi h.room hd h.mem h.rw h.lo h.env
    h.hC h.pinC h.pinK h.lbB h.imgVar h.argsImg h.argv0 h.argv0k h.a0s h.a0k h.a0nz h.noSlash h.guard h.guardk ?_
  intro s1 x hL
  refine sha_main_buf I.img I.hb I.lz I.atexit I.setvbuf hL (by rw [hL.g]; exact hat) hal h.lo h.hC ?_
  intro y hM
  have hlen := ht.argcLim
  refine sha_main_getopt I.img I.hb I.lz I.getopt hM hal h.lo h.hC h.optC h.optK h.optL h.opt
    (args := a0 :: ((p, n) :: rest).map Prod.snd) (by
      rw [ht.argc]; simp only [List.length_cons, List.length_map, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by simp at hlen; omega)) h.argv
    (fun a ha => by
      simp only [List.drop_one, List.tail_cons, List.mem_map] at ha
      obtain ⟨pn, hpn, rfl⟩ := ha
      exact (hops pn hpn).nd) ?_
  intro z hO
  refine multi_pre I.img I.hb hopA ht hO hout hjobs (by simpa using h.res) ?_
  intro v hv
  refine multi_loop M ⟨h.lo, hal, h.guardk⟩ _ _ _ _ _ v hv hops ?_
  intro t hrt
  exact task_exitPath XO s t _ (by simpa using hrt)

/-- The specification world of a file-tier run: program name `a0`, operands `ops`' names, the
file system `fs`. -/
def filesWorld (a0 : List Byte) (ops : List (Word × List Byte)) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) : Silmaril.Apps.Sha256sum.World :=
  { argv := toSpec a0 :: ops.map (fun pn => toSpec pn.2), posix, fs, stdin }

theorem isProblem_of (c : Byte) (h : Silmaril.Apps.Sha256sum.isProblemByte (UInt8.ofBitVec c) = true) :
    c = 0x5c#8 ∨ c = 0x0a#8 ∨ c = 0x0d#8 := by
  simp only [Silmaril.Apps.Sha256sum.isProblemByte, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h
  · left; have := congrArg UInt8.toBitVec h; simpa using this
  · right; left; have := congrArg UInt8.toBitVec h; simpa using this
  · right; right; have := congrArg UInt8.toBitVec h; simpa using this

/-- The machine-side restriction on a name gives the specification's (`Verbatim`). -/
theorem verbatim_of {n : List Byte} (hne : n ≠ []) (hnd : n.head? ≠ some 0x2d#8)
    (hesc : ∀ c ∈ n, c ≠ 0x5c#8 ∧ c ≠ 0x0a#8 ∧ c ≠ 0x0d#8) : FilesSpec.Verbatim (toSpec n) := by
  refine ⟨?_, by simpa [toSpec] using hne, ?_⟩
  · cases n with
    | nil => simp [FilesSpec.Plain, toSpec]
    | cons c cs =>
      simp only [FilesSpec.Plain, toSpec, List.map_cons, List.head?_cons, ne_eq, Option.some.injEq]
      intro he
      apply hnd
      have := congrArg UInt8.toBitVec he
      simp at this
      simp [this]
  · simp only [Silmaril.Apps.Sha256sum.problematic, List.any_eq_false, toSpec, List.mem_map]
    rintro _ ⟨c, hc, rfl⟩ hp
    rcases isProblem_of c hp with h | h | h
    · exact (hesc c hc).1 h
    · exact (hesc c hc).2.1 h
    · exact (hesc c hc).2.2 h

theorem linesM_spec (dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes)
    (ops : List (Word × List Byte)) :
    linesM dat ops = ofSpec (FilesSpec.fileLines dat (ops.map fun pn => toSpec pn.2)) := by
  induction ops with
  | nil => rfl
  | cons pn ops ih =>
    simp only [linesM, List.flatMap_cons, List.map_cons, FilesSpec.fileLines_cons] at ih ⊢
    rw [ih, fileLineM_spec]
    simp [ofSpec]

/-- **sha256sum FILE1 … FILEn, against the specification** `Apps.Sha256sum.sha256sum` (no open
goal): the run's exit status and standard output are the specification's, whose standard error
is empty on this tier. -/
theorem sha_main_multi_spec {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word} (I : MainImps E W b lb sr)
    (M : MultiImps E R W b lb kb sc) (hopA : E.optindA = lb + 0x204248#64) (XO : ExitOk E W b lb)
    {C : Nat → Prop} {fi : Word} {sti : St} {s : PState} {a0p : Word} {a0 : List Byte}
    {ops : List (Word × List Byte)} {g : Word}
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    (h : MainEntryF E W b lb kb sr sc C fi sti s a0p a0 (ops.map Prod.snd) g) (ht : FilesEntry E W b lb s ops g)
    (hops : ∀ pn ∈ ops, OpOk E dat pn.2) (hne : ∀ pn ∈ ops, pn.2 ≠ []) (posix : Bool)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) :
    MustQ W (Ended (Silmaril.Apps.Sha256sum.sha256sum (filesWorld a0 ops posix E.fs stdin)).status fun w =>
      w = (Silmaril.Apps.Sha256sum.sha256sum (filesWorld a0 ops posix E.fs stdin)).stdout.map UInt8.toBitVec ∧
      (Silmaril.Apps.Sha256sum.sha256sum (filesWorld a0 ops posix E.fs stdin)).stderr = []) s := by
  have hspec := FilesSpec.sha256sum_multi (filesWorld a0 ops posix E.fs stdin) (toSpec a0)
    (ops.map fun pn => toSpec pn.2) rfl (by simpa using ht.ne)
    (fun f hf => by
      simp only [List.mem_map] at hf
      obtain ⟨pn, hpn, rfl⟩ := hf
      exact verbatim_of (hne pn hpn) (hops pn hpn).nd (hops pn hpn).noEsc) dat
    (fun f hf => by
      simp only [List.mem_map] at hf
      obtain ⟨pn, hpn, rfl⟩ := hf
      exact (hops pn hpn).file) rfl
  rw [hspec]
  simp only [and_true]
  have := sha_main_multi I M hopA XO h ht hops
  rw [linesM_spec] at this
  exact this

end Silmaril.Elf.Link.Dyn.Sha256sum
