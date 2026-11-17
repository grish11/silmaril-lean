module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.MixedMain
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesErrSpec

/-! # GNU `sha256sum F1 … Fn` with refused operands, against the specification

`sha_main_mixed_spec`: `sha_main_mixed` read through `FilesSpec.sha256sum_mixed` — from `main`'s
entry (on the extended process, conditional on `Task.okExt` and `Task.errStep`), every run halts
with the exit status, standard output and standard error of `Silmaril.Apps.Sha256sum.sha256sum`
on `filesWorld a0 ops` (`stderr` from the ghost's at `main`'s entry).

Restrictions (K7's, kept): readable names are printed verbatim (no backslash, LF or CR), refused
names are gnulib-safe (`QPlain`: shown bare by `quotef`, `OpErr.fits`), no name starts with `-`,
`argv[0]` contains no `/`.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.ProcG
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports

theorem toSpec_ne {n : List Byte} (h : n ≠ []) : toSpec n ≠ [] := by
  simpa [toSpec] using h

/-- **One operand, machine and specification**: what `mixedOut` says of an operand of the tier is
`mOut` (bytes through `ofSpec`). -/
theorem mOut_spec {E : Env} {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {a0 n : List Byte} {w : Silmaril.Apps.Sha256sum.World} (hw : w.fs = E.fs) (hprog : w.prog = toSpec a0)
    (hop : MOp E dat n) :
    ofSpec (FilesSpec.mixedOut w (toSpec n)).1 = (mOut E dat a0 n).1 ∧
      ofSpec (FilesSpec.mixedOut w (toSpec n)).2.1 = (mOut E dat a0 n).2.1 ∧
      (FilesSpec.mixedOut w (toSpec n)).2.2 = (mOut E dat a0 n).2.2 := by
  rcases hop with hok | ⟨e, herr⟩
  · have hf : w.fs (toSpec n) = .ok (dat (toSpec n)) := by rw [hw]; exact hok.file
    have hm : FilesSpec.mixedOut w (toSpec n) = (FilesSpec.fileLine (toSpec n) (dat (toSpec n)), [], true) := by
      simp [FilesSpec.mixedOut, hf]
    rw [hm, mOut_ok hok, fileLineM_spec]
    exact ⟨rfl, rfl, rfl⟩
  · have hf : w.fs (toSpec n) = .openErr e := by rw [hw]; exact herr.file
    have hq : Silmaril.Apps.Sha256sum.quotef (toSpec n) = toSpec n :=
      FilesSpec.quotef_plain _ (toSpec_ne herr.plain.1) herr.plain.2
    have he : toSpec (errLineM a0 n e) = Silmaril.Apps.Sha256sum.diagE (toSpec a0) (toSpec n) e := by
      unfold errLineM; rw [toSpec_errMsg, hq]
    have hm : FilesSpec.mixedOut w (toSpec n) = ([], Silmaril.Apps.Sha256sum.diagE w.prog (toSpec n) e, false) := by
      simp [FilesSpec.mixedOut, hf]
    rw [hm, mOut_err herr]
    refine ⟨rfl, ?_, rfl⟩
    show ofSpec (Silmaril.Apps.Sha256sum.diagE w.prog (toSpec n) e) = errLineM a0 n e
    rw [hprog, ← he, ofSpec_toSpec]

theorem ofSpec_flatMap {α : Type} (f : α → Silmaril.Apps.Sha256sum.Bytes) (l : List α) :
    ofSpec (l.flatMap f) = l.flatMap fun x => ofSpec (f x) := by
  simp [ofSpec, List.map_flatMap]

/-- The specification's operand list of a file-tier run. -/
theorem filesWorld_ops (a0 : List Byte) (ops : List (Word × List Byte)) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) :
    (filesWorld a0 ops posix fs stdin).argv = toSpec a0 :: ops.map fun pn => toSpec pn.2 := rfl

/-- `argv[0]` without `/` is the specification's program name. -/
theorem filesWorld_prog {a0 : List Byte} (h : ∀ x ∈ a0, x ≠ 0x2f#8) (ops : List (Word × List Byte)) (posix : Bool)
    (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (stdin : Silmaril.Apps.Sha256sum.Stdin) : (filesWorld a0 ops posix fs stdin).prog = toSpec a0 := by
  show Silmaril.Apps.Sha256sum.progName (toSpec a0) = toSpec a0
  refine FilesSpec.progName_noSlash _ fun hm => ?_
  simp only [toSpec, List.mem_map] at hm
  obtain ⟨c, hc, he⟩ := hm
  exact h c hc (by have := congrArg UInt8.toBitVec he; simpa using this)

theorem plain_of {n : List Byte} (hnd : n.head? ≠ some 0x2d#8) : FilesSpec.Plain (toSpec n) := by
  cases n with
  | nil => simp [FilesSpec.Plain, toSpec]
  | cons c cs =>
    simp only [FilesSpec.Plain, toSpec, List.map_cons, List.head?_cons, ne_eq, Option.some.injEq]
    intro he
    apply hnd
    have := congrArg UInt8.toBitVec he
    simp at this
    simp [this]

/-- A machine operand of the tier is one of the specification's. -/
theorem mixedOp_of {E : Env} {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    {w : Silmaril.Apps.Sha256sum.World} (hw : w.fs = E.fs) {n : List Byte} (hne : n ≠ []) (hop : MOp E dat n) :
    FilesSpec.MixedOp w (toSpec n) := by
  rcases hop with hok | ⟨e, herr⟩
  · exact Or.inl ⟨verbatim_of hne hok.nd hok.noEsc, _, by rw [hw]; exact hok.file⟩
  · exact Or.inr ⟨plain_of herr.nd, ⟨toSpec_ne herr.plain.1, herr.plain.2⟩, e, by rw [hw]; exact herr.file⟩

set_option maxRecDepth 100000 in
/-- **sha256sum F1 … Fn with refused operands, against the specification** (from `main`'s entry,
on the extended process, conditional on `Task.okExt` and `Task.errStep`): every run halts with
the specification's exit status and standard output, and appends the specification's standard
error to the ghost's. -/
theorem sha_main_mixed_spec {E : Env} {R : ShaRep} {W : World} {b lb kb sr sc : Word} (I : MainImps E W b lb sr)
    (M : MultiImps E R W b lb kb sc) (hopA : E.optindA = lb + 0x204248#64) (XO : ExitOk E W b lb)
    {C : Nat → Prop} {fi : Word} {sti : St} {s : PState} {a0p : Word} {a0 : List Byte}
    {ops : List (Word × List Byte)} {g : Word}
    {dat : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.Bytes}
    (h : MainEntryF E W b lb kb sr sc C fi sti s a0p a0 (ops.map Prod.snd) g) (ht : FilesEntry E W b lb s ops g)
    (hX : MixedEntry E W b lb s a0p a0) (hops : ∀ pn ∈ ops, MOp E dat pn.2) (hne : ∀ pn ∈ ops, pn.2 ≠ [])
    (posix : Bool) (stdin : Silmaril.Apps.Sha256sum.Stdin)
    (Tok : Task.okExt E R W b lb kb sr sc s (ErrMem E W b lb (lb + 0x205378#64) a0 (s.m.core.read .rsp)))
    (Terr : Task.errStep E R W b lb kb sr sc s (ErrMem E W b lb (lb + 0x205378#64) a0 (s.m.core.read .rsp)) a0)
    (x : Silmaril.X86.Str9G.GState) (hx : XG.view x = s.m) :
    MustG XG W (fun z =>
      Ended (Silmaril.Apps.Sha256sum.sha256sum (filesWorld a0 ops posix E.fs stdin)).status (fun out =>
        out = (Silmaril.Apps.Sha256sum.sha256sum (filesWorld a0 ops posix E.fs stdin)).stdout.map UInt8.toBitVec)
        (z.view XG) ∧
      (z.view XG).g.err = s.g.err ++
        (Silmaril.Apps.Sha256sum.sha256sum (filesWorld a0 ops posix E.fs stdin)).stderr.map UInt8.toBitVec)
      ⟨x, s.g⟩ := by
  have hw : (filesWorld a0 ops posix E.fs stdin).fs = E.fs := rfl
  have hprog := filesWorld_prog h.noSlash ops posix E.fs stdin
  have hspec := FilesSpec.sha256sum_mixed (filesWorld a0 ops posix E.fs stdin) (toSpec a0)
    (ops.map fun pn => toSpec pn.2) rfl (by simpa using ht.ne)
    (fun f hf => by
      simp only [List.mem_map] at hf
      obtain ⟨pn, hpn, rfl⟩ := hf
      exact mixedOp_of hw (hne pn hpn) (hops pn hpn)) rfl
  have e1 : ofSpec ((ops.map fun pn => toSpec pn.2).flatMap
      fun f => (FilesSpec.mixedOut (filesWorld a0 ops posix E.fs stdin) f).1) = outsM E dat a0 ops := by
    rw [List.flatMap_map, ofSpec_flatMap]
    exact FilesSpec.flatMap_congr' ops fun pn hpn => (mOut_spec (dat := dat) hw hprog (hops pn hpn)).1
  have e2 : ofSpec ((ops.map fun pn => toSpec pn.2).flatMap
      fun f => (FilesSpec.mixedOut (filesWorld a0 ops posix E.fs stdin) f).2.1) = errsM E dat a0 ops := by
    rw [List.flatMap_map, ofSpec_flatMap]
    exact FilesSpec.flatMap_congr' ops fun pn hpn => (mOut_spec (dat := dat) hw hprog (hops pn hpn)).2.1
  have e3 : ((ops.map fun pn => toSpec pn.2).all
      fun f => (FilesSpec.mixedOut (filesWorld a0 ops posix E.fs stdin) f).2.2) = okM E dat a0 ops := by
    rw [List.all_map]
    exact FilesSpec.all_congr' ops fun pn hpn => (mOut_spec (dat := dat) hw hprog (hops pn hpn)).2.2
  rw [hspec]
  refine Silmaril.X86.RelIsa.Must.mono (fun _ h => h) (fun z hz => ?_)
    (sha_main_mixed I M hopA XO h ht hX hops Tok Terr x hx)
  obtain ⟨⟨w', hw1, hw2⟩, hz2⟩ := hz
  refine ⟨⟨w', ?_, ?_⟩, ?_⟩
  · rw [hw1, e3]
  · rw [hw2, ← e1]; rfl
  · rw [hz2, ← e2]; rfl

end Silmaril.Elf.Link.Dyn.Sha256sum
