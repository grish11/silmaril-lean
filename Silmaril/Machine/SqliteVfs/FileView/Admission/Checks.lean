module

import Silmaril.Machine.SqliteVfs.FileView.Admission.Thms

namespace Silmaril.Machine.SqliteVfs.FileView.Admission

open Silmaril.Formats.Sqlite.File
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead (Page Cache SlotId fill)

section Fixtures

set_option maxRecDepth 4096

private def sampleSource : Silmaril.Formats.Bytes :=
  Silmaril.Formats.Bytes.ofList
    (headerMagic ++ [2, 0, 1, 1, 0, 64, 32, 32] ++ List.replicate 488 0)

private def sampleImage : Image := (parse? sampleSource).get (by decide)
private def firstView : View := (sampleImage.page? 1).get (by decide)

example : sampleImage.header.pageSize = 512 ∧ sampleImage.pageCount = 1 ∧ firstView.length = 512 :=
  ⟨rfl, rfl, rfl⟩

example : (⟨⟨0⟩, 1, sampleImage.header.pageSize⟩ : Page).Admitted :=
  parsed_image_page_admitted (view := firstView) ⟨0⟩ (source := sampleSource) rfl rfl

end Fixtures

#print axioms parsed_image_page_admitted
#print axioms parsed_image_page_fill

end Silmaril.Machine.SqliteVfs.FileView.Admission
