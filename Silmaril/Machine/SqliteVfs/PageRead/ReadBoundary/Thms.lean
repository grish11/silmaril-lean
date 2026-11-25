module

public import Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary.Defs
import Silmaril.Proofs.Machine.SqliteVfs.PageRead.ReadBoundary.Contract

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary

open SqliteRead (Context Status BufferView)

/-- ABI admission implies the abstract VFS's signed offset and count bounds. -/
theorem read_range_of_admission (req : SqliteRead.Request) (env : Context) (safe : env.Admits req) :
    ReadRange (req.offset.toNat : Int) (req.amount.toNat : Int) :=
  Proofs.Machine.SqliteVfs.PageRead.ReadBoundary.read_range_of_admission req env safe

theorem page_admitted {binding : FileBinding} (req : SqliteRead.Request) (page : Page)
    (env : Context) (safe : env.Admits req) (aligned : MatchesPage binding req page)
    (positive : 0 < page.number) : page.Admitted :=
  Proofs.Machine.SqliteVfs.PageRead.ReadBoundary.page_admitted req page env safe aligned positive

/-- A returning handler satisfying the ABI-side snapshot law agrees with
the exact read-only page-fill outcome on full and short reads. Every
admitted status retains the caller-visible outside-buffer frame. -/
theorem returning_handler_agrees_with_fill {binding : FileBinding}
    (req : SqliteRead.Request) (page : Page) (env : Context) (file : FileState)
    (capacity : Nat) (cache : Cache) (target : SlotId) (before after : BufferView) (status : Status)
    (safe : env.Admits req) (aligned : MatchesPage binding req page) (positive : 0 < page.number)
    (live : (file.mode page.handle).isNone = false) (owned : cache target = some .vacant)
    (law : SqliteRead.Handler (file.bytes.map UInt8.toBitVec) req before after status) :
    let outcome := fill (readOnly capacity) file cache target page
    let buffer := readBytes file.bytes page.offset page.size
    SqliteRead.Framed req before after ∧
      match status with
      | .ok => outcome =
          ⟨.ok buffer, file, cache.install target page buffer, [⟨page.request, .ok buffer⟩]⟩ ∧
          ∀ i, i < page.size → after (req.buffer.toNat + i) = (buffer[i]?).map UInt8.toBitVec
      | .shortRead => outcome = ⟨.error .shortRead, file, cache, [⟨page.request, .shortRead buffer⟩]⟩ ∧
          ∀ i, i < page.size → after (req.buffer.toNat + i) = (buffer[i]?).map UInt8.toBitVec
      | .other _ => True :=
  Proofs.Machine.SqliteVfs.PageRead.ReadBoundary.returning_handler_agrees_with_fill
    req page env file capacity cache target before after status safe aligned positive live owned law

end Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary
