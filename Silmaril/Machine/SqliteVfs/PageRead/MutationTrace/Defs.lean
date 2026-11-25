module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.MutationTrace

/-- One completed successful mutation on the page's handle whose address
geometry leaves the page's interval intact. -/
inductive RetainsPage (page : Page) : Exchange → Prop where
  | write (offset : Int) (data : Bytes)
      (disjoint : page.offset + page.size ≤ offset.toNat ∨ offset.toNat + data.length ≤ page.offset) :
      RetainsPage page ⟨.write page.handle offset data, .ok ()⟩
  | truncate (size : Int) (retained : page.offset + page.size ≤ size.toNat) :
      RetainsPage page ⟨.truncate page.handle size, .ok ()⟩

end Silmaril.Machine.SqliteVfs.PageRead.MutationTrace
