module

public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Exe.Defs
import Silmaril.Elf.Staged.Reader.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Link.Dyn (ExeLoaded Resolver finfo frun relocVal slotsWith slots)
open Silmaril.Process (Memory)
open Silmaril.X86 (Word)
open Silmaril.X86.Link (Blob)
open Silmaril.Elf
open Silmaril.Elf.Link.DynElf.Elf (DynInfo Rela dynInfo relas)

private def firstAbsolute : Rela := ⟨0x10e520, 1, 195, 0⟩

private def countsAndSpans (info : DynInfo) (main plt : List Rela) : Nat × Nat × Nat × Bool × Bool :=
  (main.length, plt.length, (main.filter fun r => r.kind == 1).length,
    main.any (fun r => decide (r = firstAbsolute)),
    (main ++ plt).all (fun r => Exe.avoidsRo info.phs r.off))

private def inspect : Rd (Nat × Nat × Nat × Bool × Bool) := do
  let info ← dynInfo
  let (main, plt) ← relas info
  pure (countsAndSpans info main plt)

set_option maxRecDepth 8192 in
private theorem checked :
    inspect.run (blobRead F) = some (1468, 174, 290, true, true) :=
  Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel)

/-- The pinned file has actual readable relocation tables. Count the
type-1 entries and check the eight-byte target spans independently of
whether the loader can evaluate their values. -/
theorem relocation_spans :
    ∃ info main plt, finfo F = some info ∧ frun F (relas info) = some (main, plt) ∧
      main.length = 1468 ∧ plt.length = 174 ∧ (main.filter fun r => r.kind == 1).length = 290 ∧
      (⟨0x10e520, 1, 195, 0⟩ : Rela) ∈ main ∧
      ∀ r ∈ main ++ plt, Exe.avoidsRo info.phs r.off = true := by
  have h := checked
  change (dynInfo.bind _).run _ = _ at h
  rw [Rd.run_bind] at h
  cases hinfo : finfo F with
  | none =>
    change dynInfo.run (blobRead F) = none at hinfo
    rw [hinfo] at h
    cases h
  | some info =>
    change dynInfo.run (blobRead F) = some info at hinfo
    rw [hinfo, Option.bind_some] at h
    change ((relas info).bind _).run _ = _ at h
    rw [Rd.run_bind] at h
    cases hrelas : frun F (relas info) with
    | none =>
      change (relas info).run (blobRead F) = none at hrelas
      rw [hrelas] at h
      cases h
    | some rows =>
      change (relas info).run (blobRead F) = some rows at hrelas
      rw [hrelas, Option.bind_some] at h
      obtain ⟨main, plt⟩ := rows
      change some (countsAndSpans info main plt) = some (1468,174,290,true,true) at h
      have checks := Option.some.inj h
      simp only [countsAndSpans, Prod.mk.injEq] at checks
      obtain ⟨hm, hp, hc, he, hspan⟩ := checks
      obtain ⟨r, hr, req⟩ := List.any_eq_true.mp he
      have member : firstAbsolute ∈ main := (of_decide_eq_true req) ▸ hr
      exact ⟨info, main, plt, rfl, hrelas, hm, hp, hc, member, List.all_eq_true.mp hspan⟩

private theorem optionMapM_rejects {α β : Type} (f : α → Option β)
    {bad : α} (rejected : f bad = none) {xs : List α} (member : bad ∈ xs) :
    xs.mapM f = none := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    rcases List.mem_cons.mp member with h | h
    · subst x
      simp [List.mapM_cons, rejected]
    · have tail := ih h
      cases hx : f x <;> simp [List.mapM_cons, hx, tail]

/-- The eager evaluator rejects the actual table for every resolver. -/
theorem eager_slots_unsupported {info : DynInfo} (readInfo : finfo F = some info)
    (resolver : Resolver) : slotsWith resolver false F info = none := by
  obtain ⟨parsed, main, plt, hinfo, hrelas, _, _, _, member, _⟩ := relocation_spans
  have same := Option.some.inj (hinfo.symm.trans readInfo)
  subst info
  have rejected : (relocVal resolver F parsed ⟨0x10e520, 1, 195, 0⟩).map
      (fun value => (0x10e520, value)) = none := rfl
  have failure := optionMapM_rejects
    (fun r : Rela => (relocVal resolver F parsed r).map fun value => (r.off, value))
    rejected member
  simp [slotsWith, hrelas, failure]

/-- This pin cannot have an eager image in the current model, for any supplied
scope, bases, resolver choices or memory. -/
theorem no_eager_image {scope : List Blob} {bases : List Word} {base : Word}
    {ifunc : Word → Option Word} {resolver : Word} {memory : Memory} :
    ¬ ExeLoaded (F :: scope) (base :: bases) ifunc false resolver memory := by
  rintro ⟨file, _, info, table, _, hf, _, hi, _, computed, _, _⟩
  simp only [List.head?_cons, Option.some.injEq] at hf
  subst file
  rw [slots, eager_slots_unsupported hi] at computed
  cases computed

end Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage
