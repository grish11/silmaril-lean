module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesSpec
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.StdinTasks

/-! # GNU `sha256sum FILE1 … FILEn`, success path: the specification

The tier of `sha256sum F1 … Fn` (`n ≥ 1`) where every operand opens and reads without error and
is printed verbatim:

* `Verbatim f`: `f` does not start with `-` (not an option, not standard input), is not empty,
  and contains no backslash, LF or CR (`problematic f = false`), so that compute mode prints it
  without escaping (and no diagnostic, hence no `quotef`, is involved on this path);
* `fileLine f d`: the record `hex(SHA-256(d)) ++ "  " ++ f ++ "\n"`;
* `sha256sum_multi`: on such a world, `sha256sum w = ⟨concat of the records, [], 0⟩`;
* `fileLineM`, `fileLineM_spec`: the machine bytes of one record (what `digest_file` and the
  result line produce) are the specification's record.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.FilesSpec

open Silmaril.Apps.Sha256sum

/-- **A name printed verbatim**: not empty, not starting with `-`, and without backslash, LF or
CR. This is the restriction of the success tier on operand names. -/
structure Verbatim (f : Bytes) : Prop where
  plain : Plain f
  ne : f ≠ []
  noProblem : problematic f = false

/-- The record of a readable operand printed verbatim. -/
def fileLine (f d : Bytes) : Bytes := hexDigest d ++ [32, 32] ++ f ++ [10]

theorem computeLine_verbatim (f d : Bytes) (h : problematic f = false) :
    computeLine opts0 f d = fileLine f d := by
  simp [computeLine, recordBody, delim, opts0, h, fileLine]

/-- The records of a list of readable operands (`dat f`: the contents of `f`). -/
def fileLines (dat : Bytes → Bytes) (ops : List Bytes) : Bytes := ops.flatMap fun f => fileLine f (dat f)

theorem fileLines_cons (dat : Bytes → Bytes) (f : Bytes) (ops : List Bytes) :
    fileLines dat (f :: ops) = fileLine f (dat f) ++ fileLines dat ops := by
  simp [fileLines, List.flatMap_cons]

/-- The fold over readable operands printed verbatim. -/
theorem fold_multi (w : World) (dat : Bytes → Bytes) :
    ∀ ops : List Bytes, (∀ f ∈ ops, problematic f = false) → (∀ f ∈ ops, w.fs f = .ok (dat f)) →
      outs w opts0 ops = fileLines dat ops ∧ errs w opts0 ops = [] ∧ allOk w opts0 ops = true
  | [], _, _ => by simp [outs, errs, allOk, fileLines]
  | f :: fs, hv, hfs => by
    have hf : opOut w opts0 f = (computeLine opts0 f (dat f), [], true) := by simp [opOut, hfs f (by simp)]
    obtain ⟨h1, h2, h3⟩ := fold_multi w dat fs (fun g hg => hv g (by simp [hg])) (fun g hg => hfs g (by simp [hg]))
    refine ⟨?_, ?_, ?_⟩
    · simp only [outs, List.flatMap_cons, hf] at h1 ⊢
      rw [h1, fileLines_cons, computeLine_verbatim f _ (hv f (by simp))]
    · simp only [errs, List.flatMap_cons, hf] at h2 ⊢
      rw [h2]; rfl
    · simp only [allOk, List.all_cons, hf] at h3 ⊢
      rw [h3]; rfl

/-- **`sha256sum F1 … Fn` on readable operands printed verbatim**: the output is each operand's
record in order, no diagnostic, status 0. -/
theorem sha256sum_multi (w : World) (a0 : Bytes) (ops : List Bytes) (hargv : w.argv = a0 :: ops)
    (hne : ops ≠ []) (hv : ∀ f ∈ ops, Verbatim f) (dat : Bytes → Bytes)
    (hfs : ∀ f ∈ ops, w.fs f = .ok (dat f)) (hfull : w.stdoutFull = false) :
    sha256sum w = ⟨fileLines dat ops, [], 0⟩ := by
  rw [sha256sum_plain w a0 ops hargv hne (fun f hf => (hv f hf).plain) hfull]
  obtain ⟨h1, h2, h3⟩ := fold_multi w dat ops (fun f hf => (hv f hf).noProblem) hfs
  rw [h1, h2, h3]
  rfl

end Silmaril.Elf.Link.Dyn.Sha256sum.FilesSpec

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Byte)
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Imports

/-- The machine bytes of the result line of a readable file named `name` with contents `data`
(what `digest_file` and the result line write). -/
def fileLineM (data : Silmaril.Apps.Sha256sum.Bytes) (name : List Byte) : List Byte :=
  hexOf (sha256 (ofSpec data)) ++ [0x20#8, 0x20#8] ++ name ++ [0x0a#8]

theorem ofSpec_toSpec (l : List Byte) : ofSpec (toSpec l) = l := by
  simp only [ofSpec, toSpec, List.map_map]
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- **The machine line is the specification's record.** -/
theorem fileLineM_spec (data : Silmaril.Apps.Sha256sum.Bytes) (name : List Byte) :
    fileLineM data name = ofSpec (FilesSpec.fileLine (toSpec name) data) := by
  have hd : toSpec (ofSpec data) = data := by
    simp only [ofSpec, toSpec, List.map_map]
    induction data with
    | nil => rfl
    | cons x l ih => simp [ih]
  have hn : (toSpec name).map UInt8.toBitVec = name := ofSpec_toSpec name
  have h := stdinLine_spec (ofSpec data)
  simp only [stdinLine, Silmaril.Apps.Sha256sum.Sys.stdinRecord, hd, List.map_append] at h
  have h2 := List.append_inj_left' h (by simp [Silmaril.Apps.Sha256sum.lit])
  simp only [fileLineM, FilesSpec.fileLine, ofSpec, List.map_append] at h2 ⊢
  rw [h2, hn]
  rfl

end Silmaril.Elf.Link.Dyn.Sha256sum
