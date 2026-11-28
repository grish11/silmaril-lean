module

public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Exe.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.Check

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So (F)
open Silmaril.Elf.Link.Dyn (ExeLoaded finfo frun relocVal resolve slotsWith)
open Silmaril.Elf.Link.DynElf.Elf (DynInfo Rela relas)
open Silmaril.Process (Memory)
open Silmaril.X86 (Word)

/-- The pinned file has actual readable relocation tables. Count the
type-1 entries and check the eight-byte target spans independently of
whether the loader can evaluate their values. -/
theorem relocation_spans :
    ∃ info main plt, finfo F = some info ∧ frun F (relas info) = some (main, plt) ∧
      main.length = 1468 ∧ plt.length = 174 ∧ (main.filter fun r => r.kind == 1).length = 290 ∧
      (⟨0x10e520, 1, 195, 0⟩ : Rela) ∈ main ∧
      ∀ r ∈ main ++ plt, Exe.avoidsRo info.phs r.off = true :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.relocation_spans

/-- The pinned row binds to `sqlite3_aggregate_context` in the singleton file scope.
Its slot word is relative to the base of object 0. -/
theorem pinned_absolute_slot :
    let row : Rela := ⟨0x10e520, 1, 195, 0⟩
    ∃ info main plt, finfo F = some info ∧ frun F (relas info) = some (main, plt) ∧
      row ∈ main ∧ relocVal (resolve [F]) F info row = some (.addr 0 0x374e0) :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.pinned_absolute_slot

/-- Eager slot evaluation in the singleton scope fails on the strong reference to
`close@GLIBC_2.2.5`. -/
theorem eager_slots_without_dependencies {info : DynInfo} (readInfo : finfo F = some info) :
    slotsWith (resolve [F]) false F info = none :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.eager_slots_without_dependencies readInfo

/-- The pinned file needs a dependency scope to satisfy the eager image relation. -/
theorem no_eager_image_without_dependencies {bases : List Word} {base : Word}
    {ifunc : Word → Option Word} {resolver : Word} {memory : Memory} :
    ¬ ExeLoaded [F] (base :: bases) ifunc false resolver memory :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.no_eager_image_without_dependencies

end Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage
