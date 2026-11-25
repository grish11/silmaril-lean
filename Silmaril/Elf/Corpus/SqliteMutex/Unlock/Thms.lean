module

public import Silmaril.Elf.Corpus.SqliteMutex.Unlock.Defs
public import Silmaril.Elf.Corpus.SqliteMutex.Thms
import Silmaril.Proofs.Elf.Corpus.SqliteMutexUnlock

public section

namespace Silmaril.Elf.Corpus.SqliteMutex.Unlock

open Silmaril.Elf
open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So
open Silmaril.Elf.Link.DynElf
open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext (loadN)
open Silmaril.X86.Ext.Wire (Platform step)

/-- Both exact jump encodings are in the executable segment of the pinned file. -/
theorem code :
    CodeAt F callbackAddress.toNat callbackBytes ∧ CodeAt F pltAddress.toNat pltBytes :=
  Proofs.Elf.Corpus.SqliteMutexUnlock.code

/-- The PLT relocation selects the strong, versioned unlock reference. -/
theorem readsUnlock : readUnlock.run (blobRead F) = some (jumpSlot, unlockRef) :=
  Proofs.Elf.Corpus.SqliteMutexUnlock.readsUnlock

/-- The callback is one relative tail jump and changes only RIP. -/
theorem callback_to_plt {platform : Platform} {caller : Word} {m : MState}
    (rip : m.core.rip = callbackAddress)
    (loaded : m.memory.fetchBytes callbackAddress.toNat callbackBytes.length = some callbackBytes) :
    step platform caller m = .retired (atRip m pltAddress) :=
  Proofs.Elf.Corpus.SqliteMutexUnlock.callback_to_plt rip loaded

/-- The indirect jump reads an already populated GOT word and changes only RIP.
A readable word alone says nothing about the loader's provider or lazy binding. -/
theorem plt_to_bound_target {platform : Platform} {caller target : Word} {m : MState}
    (rip : m.core.rip = pltAddress)
    (loaded : m.memory.fetchBytes pltAddress.toNat pltBytes.length = some pltBytes)
    (bound : loadN m.memory (BitVec.ofNat 64 jumpSlot.off) 8 = some target) :
    step platform caller m = .retired (atRip m target) :=
  Proofs.Elf.Corpus.SqliteMutexUnlock.plt_to_bound_target rip loaded bound

/-- The nonnull wrapper, callback and PLT entry preserve all GPRs and memory
through entry to the bound address. This cut is before executing the target.
The wrapper's nonnull test may change flags. -/
theorem wrapper_through_plt {platform : Platform} {initial : MState} {caller target : Word}
    (entry : Entry initial caller callbackAddress) (nonNull : initial.core.read .rdi ≠ 0)
    (callbackLoaded : initial.memory.fetchBytes callbackAddress.toNat callbackBytes.length = some callbackBytes)
    (pltLoaded : initial.memory.fetchBytes pltAddress.toNat pltBytes.length = some pltBytes)
    (bound : loadN initial.memory (BitVec.ofNat 64 jumpSlot.off) 8 = some target) :
    ∃ callbackState pltState targetState,
      run platform caller 3 initial = .handlerEntry callbackState ∧
      step platform caller callbackState = .retired pltState ∧
      step platform caller pltState = .retired targetState ∧
      targetState.core.rip = target ∧ targetState.core.regs = initial.core.regs ∧
      targetState.memory = initial.memory :=
  Proofs.Elf.Corpus.SqliteMutexUnlock.wrapper_through_plt entry nonNull callbackLoaded pltLoaded bound

end Silmaril.Elf.Corpus.SqliteMutex.Unlock
