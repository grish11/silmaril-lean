module

public import Silmaril.Formats.Sqlite.File.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Defs
import Silmaril.Formats.Sqlite.File.Thms
import Silmaril.Machine.SqliteVfs.FileView.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission

open Silmaril.Formats.Sqlite.File
open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead (Page Cache SlotId fill)

private theorem parsedHeader_size {source : Silmaril.Formats.Bytes} {header : Header}
    (parsed : parseHeader? source = some header) :
    validPageSize header.pageSize = true := by
  simp only [parseHeader?] at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  obtain ⟨encoded, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨writeVersion, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨readVersion, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  obtain ⟨reserved, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  let size := if encoded == 1 then 65536 else encoded
  by_cases invalid :
      (!validPageSize size || writeVersion == 0 || !(readVersion == 1 || readVersion == 2) ||
        decide (size - reserved < 480)) = true
  · rw [ite_eq_left invalid] at parsed
    contradiction
  rw [ite_eq_right invalid] at parsed
  have sizeAllowed : validPageSize size = true := by
    cases checked : validPageSize size with
    | false => simp [checked] at invalid
    | true => rfl
  iterate 3
    obtain ⟨_, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  iterate 5
    obtain ⟨_, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  split at parsed <;> try contradiction
  iterate 10
    obtain ⟨_, _, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  cases parsed
  exact sizeAllowed

private theorem parsedImage_bounds {source : Silmaril.Formats.Bytes} {image : Image}
    (parsed : parse? source = some image) :
    validPageSize image.header.pageSize = true ∧ image.pageCount ≤ 4294967294 := by
  simp only [parse?] at parsed
  obtain ⟨header, headerParsed, parsed⟩ := Option.bind_eq_some_iff.mp parsed
  split at parsed <;> try contradiction
  let physical := source.length / header.pageSize
  let logical := if header.pageCountValid then header.rawPageCount else physical
  by_cases invalid :
      (logical == 0 || decide (logical > physical) || decide (physical > 4294967294) ||
        decide (header.freelistCount > logical) || decide (header.freelistTrunk > logical) ||
        decide (header.largestRoot > logical)) = true
  · rw [ite_eq_left invalid] at parsed
    contradiction
  rw [ite_eq_right invalid] at parsed
  cases parsed
  refine ⟨parsedHeader_size headerParsed, ?_⟩
  change logical ≤ 4294967294
  simp only [Bool.or_eq_true, decide_eq_true_eq] at invalid
  omega

theorem parsed_image_page_admitted {source : Silmaril.Formats.Bytes} {image : Image}
    {number : Nat} {view : View} (handle : Handle)
    (parsed : parse? source = some image) (found : image.page? number = some view) :
    (⟨handle, number, image.header.pageSize⟩ : Page).Admitted := by
  obtain ⟨numberPositive, numberWithin, _⟩ := Image.page?_spec image number view found
  obtain ⟨validSize, pageCountBound⟩ := parsedImage_bounds parsed
  have numberBound := Nat.le_trans numberWithin pageCountBound
  have sizeBounds : 0 < image.header.pageSize ∧ image.header.pageSize ≤ 65536 := by
    simp [validPageSize] at validSize
    omega
  have endpoint : (number - 1) * image.header.pageSize + image.header.pageSize ≤ 4294967294 * 65536 := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul (by omega) sizeBounds.2
  have countBound : image.header.pageSize ≤ maxCount :=
    Nat.le_trans sizeBounds.2 (by decide)
  have offsetBound : (number - 1) * image.header.pageSize + image.header.pageSize ≤ maxOffset :=
    Nat.le_trans endpoint (by decide)
  refine ⟨numberPositive, ?_⟩
  change ReadRange (Int.ofNat ((number - 1) * image.header.pageSize)) (Int.ofNat image.header.pageSize)
  refine ⟨Int.natCast_nonneg _, Int.natCast_pos.mpr sizeBounds.1, Int.ofNat_le.mpr countBound, ?_⟩
  change Int.ofNat ((number - 1) * image.header.pageSize + image.header.pageSize) ≤ Int.ofNat maxOffset
  exact Int.ofNat_le.mpr offsetBound

theorem parsed_image_page_fill (capacity : Nat) (file : FileState) (image : Image) (number : Nat)
    (view : View) (handle : Handle) (cache : Cache) (target : SlotId)
    {source : Silmaril.Formats.Bytes} (parsed : parse? source = some image)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false) (owned : cache target = some .vacant) :
    let page : Page := ⟨handle, number, image.header.pageSize⟩
    ∃ bytes, fill (readOnly capacity) file cache target page =
      ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ ∧
      bytes.length = view.length ∧ ∀ i, i < view.length → bytes[i]? = view.get? i :=
  Silmaril.Machine.SqliteVfs.FileView.image_page_fill capacity file image number view handle cache target
    snapshot found live (parsed_image_page_admitted handle parsed found).2 owned

end Silmaril.Proofs.Machine.SqliteVfs.FileView.Admission
