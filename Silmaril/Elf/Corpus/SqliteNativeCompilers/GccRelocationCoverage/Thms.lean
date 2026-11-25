module

public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Exe.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.Check

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So (F)
open Silmaril.Elf.Link.Dyn (ExeLoaded Resolver finfo frun slotsWith)
open Silmaril.Elf.Link.DynElf.Elf (DynInfo Rela relas)
open Silmaril.Process (Memory)
open Silmaril.X86 (Word)
open Silmaril.X86.Link (Blob)

/-- The pinned file has actual readable relocation tables. Count the
type-1 entries and check the eight-byte target spans independently of
whether the loader can evaluate their values. -/
theorem relocation_spans :
    ∃ info main plt, finfo F = some info ∧ frun F (relas info) = some (main, plt) ∧
      main.length = 1468 ∧ plt.length = 174 ∧ (main.filter fun r => r.kind == 1).length = 290 ∧
      (⟨0x10e520, 1, 195, 0⟩ : Rela) ∈ main ∧
      ∀ r ∈ main ++ plt, Exe.avoidsRo info.phs r.off = true :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.relocation_spans

/-- The eager evaluator rejects the actual table for every resolver. -/
theorem eager_slots_unsupported {info : DynInfo} (readInfo : finfo F = some info)
    (resolver : Resolver) : slotsWith resolver false F info = none :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.eager_slots_unsupported readInfo resolver

/-- This pin cannot have an eager image in the current model, for any supplied
scope, bases, resolver choices or memory. -/
theorem no_eager_image {scope : List Blob} {bases : List Word} {base : Word}
    {ifunc : Word → Option Word} {resolver : Word} {memory : Memory} :
    ¬ ExeLoaded (F :: scope) (base :: bases) ifunc false resolver memory :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.no_eager_image

end Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage
