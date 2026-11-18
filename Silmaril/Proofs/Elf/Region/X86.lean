module

public import Silmaril.Elf.Region.X86.Defs

@[expose] public section
namespace Silmaril.Elf.Region.X86.Proofs
open Silmaril.Process

 theorem window_loaded {image : LPS.Image} {segment : LPS.Segment} {m : Silmaril.X86.MState}
    (loaded : Silmaril.X86.Link.FnSpec.ImageLoaded image m) (member : segment ∈ image.segments)
    (executable : segment.executable = true) (bytes : segment.bytes.length = segment.size)
    (limit : segment.base + segment.size < addressLimit) {offset length : Nat}
    (fits : offset + length ≤ segment.size) : (window segment offset length).LoadedIn m.memory := by
  intro off len hfit
  have size : ((segment.bytes.drop offset).take length).length = length := by
    simp only [List.length_take, List.length_drop, bytes]
    omega
  change off + len ≤ ((segment.bytes.drop offset).take length).length at hfit
  rw [size] at hfit
  let bs := (((segment.bytes.drop offset).take length).drop off).take len
  have blen : bs.length = len := by
    dsimp [bs]
    simp only [List.length_take, List.length_drop, size]
    omega
  have backing : ∀ i (hi : i < len),
      m.memory.bytes.get? (segment.base + offset + off + i) = some bs[i] := by
    intro i hi
    have index : offset + off + i < segment.bytes.length := by rw [bytes]; omega
    have byte := loaded segment member (offset + off + i) (by omega)
      segment.bytes[offset + off + i] (List.getElem?_eq_getElem index)
    have eq : bs[i] = segment.bytes[offset + off + i] := by
      dsimp [bs]
      simp only [List.getElem_take, List.getElem_drop]
      congr 1; omega
    simpa only [Nat.add_assoc, eq] using byte.1
  have perm : m.memory.Permitted .execute (segment.base + offset + off) bs.length := by
    rw [Memory.Permitted, Memory.checkSpan_iff, blen]
    refine ⟨by omega, by omega, ?_⟩
    intro i hi
    have index : offset + off + i < segment.bytes.length := by rw [bytes]; omega
    have byte := loaded segment member (offset + off + i) (by omega)
      segment.bytes[offset + off + i] (List.getElem?_eq_getElem index)
    simpa only [Nat.add_assoc] using byte.2 executable
  have read := Memory.readWith_eq m.memory .execute (segment.base + offset + off) bs perm
    (fun i hi => backing i (by omega))
  simpa only [blen, Memory.fetchBytes, window, bs] using read

 theorem parsed_window_loaded {file : Silmaril.Formats.ELF.Bytes}
    {records : LPS.ELFImage.Records} {segment : LPS.Segment} {m : Silmaril.X86.MState}
    (parsed : LPS.ELFImage.parse LPS.ELFImage.x86Policy file = some records)
    (loaded : Silmaril.X86.Link.FnSpec.ImageLoaded (records.image file) m)
    (member : segment ∈ (records.image file).segments) (executable : segment.executable = true)
    {offset length : Nat} (fits : offset + length ≤ segment.size) :
    (window segment offset length).LoadedIn m.memory := by
  obtain ⟨bytes, _, bound⟩ := LPS.ELFImage.parsed_segment_wellformed parsed member
  exact window_loaded loaded member executable bytes (by
    change segment.base + segment.size < 2 ^ 64
    change segment.base + segment.size ≤ 0x7ffffffff000 at bound
    omega) fits

end Silmaril.Elf.Region.X86.Proofs
