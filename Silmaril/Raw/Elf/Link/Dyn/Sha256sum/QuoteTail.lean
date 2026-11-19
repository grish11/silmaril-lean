module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteProRun
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteExitRun
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.QuoteIter
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesErrX
public import Silmaril.Elf.Link.Dyn.Loader.Thms

/-! # GNU `sha256sum`: `quotef` on plain names, and `digest_file` on a refused name

PROVED (standard axioms):

* **`task_quotefTail`**: `Task.quotefTail` from `task_quotePro`, `task_quoteIter`, `task_quoteExit`
  (`task_quotefTail_of`);
* **`task_quotefX_ok`**: `Task.quotefX` (gnulib's `quotef` on a plain name, on `procG Str9G.extendsOpen9`);
* **`task_digestOpenErrX_ok`**: `Task.digestOpenErrX` (`digest_file`'s refused-name path, plain names,
  on the extended process).

The `_ok` forms assume the executable's base is 16-byte aligned (`quotef`'s `movdqa`). The `_paged`
forms derive it from the loader fact `PageBase` (the loader maps every object at a page boundary;
`ExeLoadedP` = `ExeLoaded` with it): **`task_quotefX_paged`**, **`task_digestOpenErrX_paged`**,
**`task_digestOpenErrX_loaded`** (from `ExeLoadedP`), with no other assumption.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum

open Silmaril.X86 (Word)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Imports

/-- **`Task.quotefTail`**. -/
theorem task_quotefTail {E : Env} {W : World} {b lb : Word} : Task.quotefTail E W b lb :=
  task_quotefTail_of task_quotePro task_quoteIter task_quoteExit

/-- **`Task.quotefX`** (base 16-byte aligned). -/
theorem task_quotefX_ok {E : Env} {W : World} {b lb : Word} (hal : b.toNat % 16 = 0) : Task.quotefX E W b lb :=
  task_quotefX hal task_quotefTail

/-- **`Task.digestOpenErrX`** (base 16-byte aligned). -/
theorem task_digestOpenErrX_ok {E : Env} {R : ShaRep} {W : World} {b lb kb pinA : Word}
    (hal : b.toNat % 16 = 0) : Task.digestOpenErrX E R W b lb kb pinA :=
  task_digestOpenErrX_of_tail hal task_quotefTail

/-- **`Task.quotefX`** for an executable mapped at a page-aligned base (loader fact `PageBase`). -/
theorem task_quotefX_paged {E : Env} {W : World} {b lb : Word} {bs : List Word} (hp : PageBase (b :: bs)) :
    Task.quotefX E W b lb :=
  task_quotefX_ok hp.mod16

/-- **`Task.digestOpenErrX`** for an executable mapped at a page-aligned base (loader fact `PageBase`). -/
theorem task_digestOpenErrX_paged {E : Env} {R : ShaRep} {W : World} {b lb kb pinA : Word} {bs : List Word}
    (hp : PageBase (b :: bs)) : Task.digestOpenErrX E R W b lb kb pinA :=
  task_digestOpenErrX_ok hp.mod16

/-- **`Task.digestOpenErrX`** for an executable loaded at `b` (`ExeLoadedP`: the loader relation with
page-aligned bases). -/
theorem task_digestOpenErrX_loaded {E : Env} {R : ShaRep} {W : World} {b lb kb pinA res : Word}
    {bs : List Word} {scope : List Silmaril.X86.Link.Blob} {ifn : Word → Option Word} {lazy : Bool}
    {mem : Silmaril.Process.Memory} (h : ExeLoadedP scope (b :: bs) ifn lazy res mem) :
    Task.digestOpenErrX E R W b lb kb pinA :=
  task_digestOpenErrX_paged h.2

end Silmaril.Elf.Link.Dyn.Sha256sum
