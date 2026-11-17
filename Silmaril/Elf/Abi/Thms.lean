module

public import Silmaril.Elf.Abi.Defs

/-! # ABI conformance of an ELF function: theorems

* `AbiConforms.placement`: a row names a file that admits a load base;
* `not_abiConforms_of_noPlacement`: **regression**: on a file that admits no load base (an
  `ET_EXEC` whose `PT_LOAD` has `p_filesz > p_memsz` or reaches past `2^47`, …) no function
  conforms, for any spec and any machine: the rebased-conformance conjunct cannot be vacuous.
-/

@[expose] public section

namespace Silmaril.Elf.Abi

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.X86.Link (Blob)

variable {A : AbiDef} {M : Mach} {mode : Mode} {hdr : HeaderSrc} {f : String} {p : A.V.Proto}
  {F : Blob} {b : Binding} {c : Code} {frame : Nat} {S : CallSpec A.V p}

theorem AbiConforms.placement (h : AbiConforms A M mode hdr f p F b c frame S) :
    ∃ base, Placement F base :=
  h.2.2.1

theorem not_abiConforms_of_noPlacement (hno : ∀ base, ¬ Placement F base) :
    ¬ AbiConforms A M mode hdr f p F b c frame S :=
  fun h => let ⟨base, hb⟩ := h.placement; hno base hb

end Silmaril.Elf.Abi

end
