module

public import Silmaril.Machine.SqliteRead.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary

/-- A caller-supplied binding from an ABI-side file pointer to a handle in
one abstract backing. -/
abbrev FileBinding := BitVec 64 → Option Handle

/-- The pointer binding, file offset, and transfer count agree with the page. -/
structure MatchesPage (binding : FileBinding) (req : SqliteRead.Request) (page : Page) : Prop where
  handle : binding req.file = some page.handle
  offset : req.offset.toNat = page.offset
  amount : req.amount.toNat = page.size

end Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary
