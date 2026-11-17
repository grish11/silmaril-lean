module

public import Silmaril.Elf.Abi.Defs
import Silmaril.Proofs.Elf.Abi.Basic

/-! # ABI conformance of an ELF function: theorems

* `AbiConforms.placement`: a row names a file that admits a load base;
* `not_abiConforms_of_noPlacement`: **regression**: on a file that admits no load base (an
  `ET_EXEC` whose `PT_LOAD` has `p_filesz > p_memsz` or reaches past `2^47`, …) no function
  conforms, for any spec and any machine: the rebased-conformance conjunct cannot be vacuous;
* `Present.not_absent`: **`absent` cannot be faked**: a function some symbol table of the file
  defines (in any table and version) is not absent, so an `absent` exclusion of it is refused;
* `CodeOf.bytes_unique`, `not_codeOf_of_bytes`: **the bytes are the file's**: two codes of one
  binding at one address with bytes of one length have the same bytes, so a code whose bytes
  differ from the file's (one byte changed) is the function of no binding.
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

theorem Present.not_absent (h : Present F f) : ¬ Absent F f := by
  rintro ⟨B, hB, hall⟩
  obtain ⟨A, hA, t, s, hs, hn, hi, -⟩ := h
  cases (Option.some.inj (hA.symm.trans hB) : A = B)
  exact hi (hall t s hs hn)

theorem CodeOf.bytes_unique {c' : Code} {b' : Binding} {f' : String} (h : CodeOf F b f c)
    (h' : CodeOf F b' f' c') (hb : c.base = c'.base) (hl : c.bytes.length = c'.bytes.length) :
    c.bytes = c'.bytes :=
  Silmaril.Proofs.Elf.Abi.codeAt_unique h.2.1 (hb ▸ h'.2.1) hl

theorem not_codeOf_of_bytes {c' : Code} {b' : Binding} {f' : String} (h : CodeOf F b f c)
    (hb : c.base = c'.base) (hl : c.bytes.length = c'.bytes.length) (hne : c.bytes ≠ c'.bytes) :
    ¬ CodeOf F b' f' c' :=
  fun h' => hne (h.bytes_unique h' hb hl)

end Silmaril.Elf.Abi

end
