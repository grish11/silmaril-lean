module

public import Silmaril.Containers.SqliteVfs.Completed.Defs
public import Silmaril.Containers.SqliteVfs.ReadEntry.Defs
public import Silmaril.Elf.Corpus.SqliteRead.Defs
import Silmaril.Proofs.Containers.SqliteVfs.NativeReadEntry.Dispatch

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.NativeReadEntry

open Silmaril.Containers
open Silmaril.Containers.SqliteVfs (machine)
open Silmaril.Containers.SqliteVfs.Completed (completed)
open Silmaril.Containers.SqliteVfs.ReadEntry (projectEntry)
open Silmaril.Elf.Corpus.SqliteRead (Dispatches observe run)
open Silmaril.Machine.Behaviour.Observable (Safe)
open Silmaril.Machine.SqliteVfs (Handler)
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary (FileBinding)
open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext.Wire (Platform)

/-- The admitted three-step cut in the pinned `readDbPage` dispatch reaches
handler entry. Its aligned request projects to one pending logical VFS
receive, with the initial backing and zero completed exchanges. -/
theorem pinned_readDbPage_pending {State : Type} (handler : Handler State)
    (state : State) {platform : Platform} {initial : MState} {elfPage : Elf.Corpus.SqliteRead.PageRead}
    {methods target : Word} {env : Machine.SqliteRead.Context}
    {binding : FileBinding} {page : Machine.SqliteVfs.PageRead.Page}
    (entry : Elf.Corpus.SqliteRead.Entry initial elfPage methods target)
    (safe : Safe ((Machine.SqliteRead.contract env).spec elfPage.request))
    (bound : binding elfPage.file = some page.handle)
    (number : page.number = elfPage.index + 1) (size : page.size = elfPage.count.toNat) :
    ∃ next, Dispatches platform initial elfPage.request target next ∧
      page.Admitted ∧
      projectEntry binding (observe (run platform 3 initial)) = some (.recv page.request) ∧
      (machine handler).Exec Mach.seqPolicy (.idle state) [.recv page.request]
        (.pending state page.request) ∧ completed [.recv page.request] = [] :=
  Proofs.Containers.SqliteVfs.NativeReadEntry.pinned_readDbPage_pending
    handler state entry safe bound number size

end Silmaril.Containers.SqliteVfs.NativeReadEntry
