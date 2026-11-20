module

public import CompilesToExamples.Straight.Defs
public import Silmaril.Machine.Region.X86.Defs

@[expose] public section
namespace CompilesToExamples.Explorer

open CompilesToExamples.Straight.O2 (add3 add3Listing)
open Silmaril.Machine.Region.X86 (Candidate propose)
open Silmaril.X86.Decompile (Decoded)

/-- The existing decoded listing at the compilation model's placement.
The `ret` leaves its candidate boundary Top; this is not a valid-region judgment. -/
def add3Block : Candidate :=
  propose (add3Listing.map fun (offset, instruction, length) =>
    ⟨add3.addr + offset, instruction, length⟩) add3.addr

theorem add3Block_shape : add3Block.entry = 0x401000 ∧
    add3Block.listing.map Decoded.addr = [0x401000, 0x401002, 0x401005] ∧
    add3Block.allowance = .top := ⟨rfl, rfl, rfl⟩

end CompilesToExamples.Explorer
