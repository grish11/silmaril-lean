module

public import Silmaril.Machine.Region.Defs
public import Silmaril.Process.LPS.MemImage
public import Silmaril.Process.Memory

@[expose] public section
namespace Silmaril.Process.Region
open Silmaril.Machine.Region

/-- Sparse virtual memory with execute checks. Missing backing/permission
remains none; this does not turn absence into an empty region. -/
def executableSource (memory : Memory) : ByteSource :=
  ⟨fun n => (memory.fetchBytes n 1).bind fun bytes => bytes.head?.map fun b => UInt8.ofNat b.toNat⟩

/-- LPS loaded-image segments stay virtual and executable. The bytes are
already loaded, including any loader-established zero-filled tail. -/
def loadedMapping (segment : LPS.Segment) : Option Mapping :=
  if segment.executable then
    some ⟨⟨.virtual, ⟨segment.base, segment.base + segment.size, Nat.le_add_right _ _⟩⟩,
      segment.base⟩
  else none

/-- Bytes of the existing LPS image, with no first-owner guess on overlap. -/
def imageByte (image : LPS.Image) (address : Nat) : Option UInt8 :=
  let owners := image.segments.filter fun s => s.base ≤ address && address < s.base + s.size
  match owners with
  | [s] => (s.byteAt (address - s.base)).map fun b => UInt8.ofNat b.toNat
  | _ => none

/-- Omitting data supplies no assumptions about its values. A downstream
semantics must quantify over compatible memories; it may not use zeros. -/
def ofLoaded (image : LPS.Image) (includeData : Bool) : LoadedImage :=
  let source : ByteSource := ⟨imageByte image⟩
  ⟨⟨source, image.segments.filterMap loadedMapping⟩, if includeData then some source else none⟩
end Silmaril.Process.Region
