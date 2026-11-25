module

public import Silmaril.Formats.Sqlite.File.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission.Bounds

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.FileView.Admission

open Silmaril.Formats.Sqlite.File
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead (Page Cache SlotId fill)

/-- The accepted image geometry and successful page lookup imply the VFS
signed count and offset bounds for this one page. -/
theorem parsed_image_page_admitted {source : Silmaril.Formats.Bytes} {image : Image}
    {number : Nat} {view : View} (handle : Handle)
    (parsed : parse? source = some image) (found : image.page? number = some view) :
    (⟨handle, number, image.header.pageSize⟩ : Page).Admitted :=
  Proofs.Machine.SqliteVfs.FileView.Admission.parsed_image_page_admitted handle parsed found

/-- An owned fill for a page of the parsed image uses the derived read bounds.
It installs exactly the view's bytes and records one successful exchange. -/
theorem parsed_image_page_fill (capacity : Nat) (file : FileState) (image : Image) (number : Nat)
    (view : View) (handle : Handle) (cache : Cache) (target : SlotId)
    {source : Silmaril.Formats.Bytes} (parsed : parse? source = some image)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false) (owned : cache target = some .vacant) :
    let page : Page := ⟨handle, number, image.header.pageSize⟩
    ∃ bytes, fill (readOnly capacity) file cache target page =
      ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      bytes.length = view.length ∧ ∀ i, i < view.length → bytes[i]? = view.get? i :=
  Proofs.Machine.SqliteVfs.FileView.Admission.parsed_image_page_fill
    capacity file image number view handle cache target parsed snapshot found live owned

end Silmaril.Machine.SqliteVfs.FileView.Admission
