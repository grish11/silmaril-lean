module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesErr
public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.FilesQuoteX

/-! # GNU `sha256sum`: `digest_file` on a refused name, on the extended process

`Task.digestOpenErr` (`FilesErr.task_digestOpenErr`) is proved over `Proc.proc` given
`Task.quotef`, which no `proc` run can meet: `quotef` starts with SSE moves (`FilesQuoteStop`).
Over the extended process `procG Str9G.extendsOpen9` (the image machine with SSE moves) the same
path holds for plain names given `Task.quotefX` (`FilesQuoteX`), and so given `Task.quotefTail`:

* **`task_digestOpenErrX`**: `Task.quotefX → Task.digestOpenErrX` (every `proc` piece of
  `digest_file` is lifted by `ProcG.mustG_of_mustQ`; `quotef` is called on `procG`);
* **`task_digestOpenErrX_of_tail`**: with the executable's base 16-byte aligned,
  `Task.quotefTail → Task.digestOpenErrX`.

PROVED (standard axioms). Open: `Task.quotefTail` (`quotearg_n_options` and `quotef`'s epilogue on
`proc`).
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

/-- **`digest_file` on a name the file system refuses, on the extended process** (plain names). -/
def Task.digestOpenErrX (E : Env) (R : ShaRep) (W : World) (b lb kb pinA : Word) : Prop :=
  DigImps E R W b lb kb → ErrImps E W lb pinA → ∀ (Q : XPS → Prop) (y : XPS) (p : List Byte) (e : Silmaril.Apps.Sha256sum.Errno) (g : Word)
    (prog : List Byte), QPlain p → DigEntryE E W b lb kb pinA (y.view XG) p e g prog →
    (∀ z, DigErrExit E W b (y.view XG) (z.view XG) p e prog → MustG XG W Q z) → MustG XG W Q y

theorem xview_mk {t : PState} {x' : Silmaril.X86.Str9G.GState} (hx : XG.view x' = t.m) :
    GState.view XG (⟨x', t.g⟩ : XPS) = t := by
  show (⟨XG.view x', t.g⟩ : PState) = t; rw [hx]

/-- **`Task.digestOpenErrX` from `Task.quotefX`.** -/
theorem task_digestOpenErrX {E : Env} {R : ShaRep} {W : World} {b lb kb pinA : Word}
    (hq : Task.quotefX E W b lb) : Task.digestOpenErrX E R W b lb kb pinA := by
  intro I K Q y p e g prog hP hE k
  have h : MustQ W (fun t => ∀ x', XG.view x' = t.m → MustG XG W Q ⟨x', t.g⟩) (y.view XG) :=
    sha_digestOpenErr_for I K (fun s' hQE hk => .done fun x' hx' => by
        refine hq Q ⟨x', s'.g⟩ p (by rw [xview_mk hx']; exact hQE) hP (fun z hz => ?_)
        rw [xview_mk hx'] at hz
        exact mustG_of_mustQ XG rfl (hk _ hz))
      hE (fun t ht => .done fun x' hx' => k ⟨x', t.g⟩ (by rw [xview_mk hx']; exact ht))
  exact mustG_of_mustQ XG rfl h

/-- **`Task.digestOpenErrX` from `Task.quotefTail`** (base 16-byte aligned). -/
theorem task_digestOpenErrX_of_tail {E : Env} {R : ShaRep} {W : World} {b lb kb pinA : Word}
    (hal : b.toNat % 16 = 0) (hT : Task.quotefTail E W b lb) : Task.digestOpenErrX E R W b lb kb pinA :=
  task_digestOpenErrX (task_quotefX hal hT)

end Silmaril.Elf.Link.Dyn.Sha256sum
