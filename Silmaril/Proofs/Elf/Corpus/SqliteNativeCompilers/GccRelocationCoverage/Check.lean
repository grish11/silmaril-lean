module

public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Exe.Defs
import Silmaril.Elf.Staged.Reader.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Link.Dyn (ExeLoaded abs64Ref bindVal defVal finfo frun relocVal resolve resolveFrom
  slotsWith slots)
open Silmaril.Elf.Exe (avoidsRo)
open Silmaril.Process (Memory)
open Silmaril.X86 (Word)
open Silmaril.Elf.Link.DynElf.Elf (Def DynInfo Ref Rela dynInfo lookupDef relas)

private def firstAbsolute : Rela := ⟨0x10e520, 1, 195, 0⟩
private def closeAbsolute : Rela := ⟨0x112580, 1, 26, 0⟩

private def countsAndSpans (info : DynInfo) (main plt : List Rela) :
    Nat × Nat × Nat × Bool × Bool × Bool :=
  (main.length, plt.length, (main.filter fun r => r.kind == 1).length,
    main.any (fun r => decide (r = firstAbsolute)),
    main.any (fun r => decide (r = closeAbsolute)),
    (main ++ plt).all (fun r => avoidsRo info.phs r.off))

private def inspect : Rd (Nat × Nat × Nat × Bool × Bool × Bool) := do
  let info ← dynInfo
  let (main, plt) ← relas info
  pure (countsAndSpans info main plt)

set_option maxRecDepth 8192 in
private theorem checked :
    inspect.run (blobRead F) = some (1468, 174, 290, true, true, true) :=
  Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel)

private theorem checked_tables :
    ∃ info main plt, finfo F = some info ∧ frun F (relas info) = some (main, plt) ∧
      main.length = 1468 ∧ plt.length = 174 ∧ (main.filter fun r => r.kind == 1).length = 290 ∧
      firstAbsolute ∈ main ∧ closeAbsolute ∈ main ∧
      ∀ r ∈ main ++ plt, avoidsRo info.phs r.off = true := by
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
      change some (countsAndSpans info main plt) = some (1468, 174, 290, true, true, true) at h
      have checks := Option.some.inj h
      simp only [countsAndSpans, Prod.mk.injEq] at checks
      obtain ⟨hm, hp, hc, hfirst, hclose, hspan⟩ := checks
      obtain ⟨_, hr, req⟩ := List.any_eq_true.mp hfirst
      obtain ⟨_, hs, seq⟩ := List.any_eq_true.mp hclose
      exact ⟨info, main, plt, rfl, hrelas, hm, hp, hc, (of_decide_eq_true req) ▸ hr,
        (of_decide_eq_true seq) ▸ hs, List.all_eq_true.mp hspan⟩

theorem relocation_spans :
    ∃ info main plt, finfo F = some info ∧ frun F (relas info) = some (main, plt) ∧
      main.length = 1468 ∧ plt.length = 174 ∧ (main.filter fun r => r.kind == 1).length = 290 ∧
      (⟨0x10e520, 1, 195, 0⟩ : Rela) ∈ main ∧
      ∀ r ∈ main ++ plt, avoidsRo info.phs r.off = true := by
  obtain ⟨info, main, plt, hi, ht, hm, hp, hc, hfirst, _, hspan⟩ := checked_tables
  exact ⟨info, main, plt, hi, ht, hm, hp, hc, hfirst, hspan⟩

private def inspectBinding (index : Nat) : Rd (Ref × Option Def) := do
  let info ← dynInfo
  let ref ← abs64Ref info index
  let defn ← lookupDef info ref false
  pure (ref, defn)

private theorem binding_of_check {index : Nat} {ref : Ref} {defn : Option Def}
    (checked : (inspectBinding index).run (blobRead F) = some (ref, defn)) :
    ∃ info, finfo F = some info ∧ frun F (abs64Ref info index) = some ref ∧
      frun F (lookupDef info ref false) = some defn := by
  change ((dynInfo.bind _).run _) = _ at checked
  rw [Rd.run_bind] at checked
  obtain ⟨info, hi, checked⟩ := Option.bind_eq_some_iff.mp checked
  change ((abs64Ref info index).bind _).run _ = _ at checked
  rw [Rd.run_bind] at checked
  obtain ⟨ref', href, checked⟩ := Option.bind_eq_some_iff.mp checked
  change ((lookupDef info ref' false).bind _).run _ = _ at checked
  rw [Rd.run_bind] at checked
  obtain ⟨defn', hdef, checked⟩ := Option.bind_eq_some_iff.mp checked
  cases checked
  exact ⟨info, hi, href, hdef⟩

private def aggregateContext : Ref := ⟨"sqlite3_aggregate_context".toList.map Char.toNat, false, none⟩
private def closeRef : Ref := ⟨"close".toList.map Char.toNat, false,
  some ⟨"GLIBC_2.2.5".toList.map Char.toNat, 0x09691a75, false⟩⟩

set_option maxRecDepth 8192 in
theorem pinned_absolute_slot :
    let row : Rela := ⟨0x10e520, 1, 195, 0⟩
    ∃ info main plt, finfo F = some info ∧ frun F (relas info) = some (main, plt) ∧
      row ∈ main ∧ relocVal (resolve [F]) F info row = some (.addr 0 0x374e0) := by
  have checked : (inspectBinding 195).run (blobRead F) =
      some (aggregateContext, some ⟨0x374e0, false, false⟩) :=
    Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel)
  obtain ⟨info, hi, href, hdef⟩ := binding_of_check checked
  obtain ⟨parsed, main, plt, hp, ht, _, _, _, member, _⟩ := relocation_spans
  have same := Option.some.inj (hi.symm.trans hp)
  subst parsed
  refine ⟨info, main, plt, hi, ht, member, ?_⟩
  change (frun F (abs64Ref info 195)).bind _ = _
  rw [href]
  simp [resolve, resolveFrom, hi, hdef, bindVal, defVal]

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

set_option maxRecDepth 8192 in
theorem eager_slots_without_dependencies {info : DynInfo} (readInfo : finfo F = some info) :
    slotsWith (resolve [F]) false F info = none := by
  have checked : (inspectBinding 26).run (blobRead F) = some (closeRef, none) :=
    Rd.run_mono (sub_kbytes K.wf_true K.toByteArray_eq) _ _ (by decide +kernel)
  obtain ⟨parsed, hi, href, hdef⟩ := binding_of_check checked
  have same := Option.some.inj (readInfo.symm.trans hi)
  subst parsed
  obtain ⟨parsed, main, plt, hp, hrelas, _, _, _, _, member, _⟩ := checked_tables
  have same := Option.some.inj (readInfo.symm.trans hp)
  subst parsed
  have rejected : relocVal (resolve [F]) F info closeAbsolute = none := by
    change (frun F (abs64Ref info 26)).bind _ = _
    rw [href]
    have strong : closeRef.weak = false := rfl
    simp [resolve, resolveFrom, readInfo, hdef, bindVal, strong]
  have failure := optionMapM_rejects
    (fun r : Rela => (relocVal (resolve [F]) F info r).map fun value => (r.off, value))
    (by rw [rejected]; rfl) member
  simp [slotsWith, hrelas, failure]

theorem no_eager_image_without_dependencies {bases : List Word} {base : Word}
    {ifunc : Word → Option Word} {resolver : Word} {memory : Memory} :
    ¬ ExeLoaded [F] (base :: bases) ifunc false resolver memory := by
  rintro ⟨file, _, info, table, _, hf, _, hi, _, computed, _, _⟩
  simp only [List.head?_cons, Option.some.injEq] at hf
  subst file
  rw [slots, eager_slots_without_dependencies hi] at computed
  cases computed

end Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage
