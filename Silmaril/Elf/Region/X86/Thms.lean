module

public import Silmaril.Elf.Region.X86.Defs
import Silmaril.Proofs.Elf.Region.X86

@[expose] public section
namespace Silmaril.Elf.Region.X86
open Silmaril.Process

/-- Any executable window in a checked x86 ELF loader image satisfies the
existing listing's actual fetch contract. This includes empty endpoint reads;
the x86 task-size bound keeps the endpoint strictly below the address limit. -/
theorem parsed_window_loaded {file : Silmaril.Formats.ELF.Bytes}
    {records : LPS.ELFImage.Records} {segment : LPS.Segment} {m : Silmaril.X86.MState}
    (parsed : LPS.ELFImage.parse LPS.ELFImage.x86Policy file = some records)
    (loaded : Silmaril.X86.Link.FnSpec.ImageLoaded (records.image file) m)
    (member : segment ∈ (records.image file).segments) (executable : segment.executable = true)
    {offset length : Nat} (fits : offset + length ≤ segment.size) :
    (window segment offset length).LoadedIn m.memory :=
  Proofs.parsed_window_loaded parsed loaded member executable fits

/-- Placement plus successful decoding feeds the existing operational edge
proof directly; no function-extraction premise or relocated-call guess. -/
theorem placed_listing_step {file : Silmaril.Formats.ELF.Bytes}
    {records : LPS.ELFImage.Records} {segment : LPS.Segment} {m t : Silmaril.X86.MState}
    (parsed : LPS.ELFImage.parse LPS.ELFImage.x86Policy file = some records)
    (loaded : Silmaril.X86.Link.FnSpec.ImageLoaded (records.image file) m)
    (member : segment ∈ (records.image file).segments) (executable : segment.executable = true)
    {offset length fuel : Nat} (fits : offset + length ≤ segment.size)
    {ds : List Silmaril.X86.Decompile.Decoded} {d : Silmaril.X86.Decompile.Decoded}
    (decoded : (window segment offset length).decode? fuel = some ds)
    (hd : d ∈ ds) (pc : m.core.rip.toNat = d.addr) {ret : Silmaril.X86.Word}
    (step : (Silmaril.Machine.Region.X86.system ret).step m [] t) :
    (Silmaril.Machine.Region.X86.instructionTargets d).Allows t.core.rip.toNat :=
  Silmaril.Machine.Region.X86.listing_step decoded
    (parsed_window_loaded parsed loaded member executable fits) hd pc step

end Silmaril.Elf.Region.X86
