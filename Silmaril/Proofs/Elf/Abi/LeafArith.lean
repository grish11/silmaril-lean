module

public import Silmaril.Elf.Abi.LeafArith.Defs
public import Silmaril.Elf.Staged.Pinned.LeafArith.Thms
public import Silmaril.Elf.Staged.Reader.Thms
public import Silmaril.Machine.Abi.Conformance.LeafArith.Thms

/-! # ABI conformance rows of `leaf-arith`: proofs

The file facts are one kernel read each on the file's kernel bytes (the per-part reader's
`parses` and `codeAt_of_kbytes`); the conformance is `Machine.Abi.Conformance.LeafArith`. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.LeafArith

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.LeafArith
open Silmaril.Elf.Abi Silmaril.Elf.Abi.LeafArith
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.LeafArith

/-- The file maps the 181 transcribed bytes at `0x401370`. -/
theorem codeAt : CodeAt F 0x401370 Silmaril.X86.Ladder.LeafArith.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel)

theorem clamp_code : CodeOf F (sel "clamp_i32") "clamp_i32" clampCode :=
  ⟨rfl, ⟨⟨19, 4199328, 19, false, false⟩, ⟨_, parses, by decide +kernel⟩, by decide, rfl, rfl, rfl⟩,
    codeAt, fun _ h => nomatch h⟩

theorem sat_code : CodeOf F (sel "sat_add_u32") "sat_add_u32" satCode :=
  ⟨rfl, ⟨⟨10, 4199424, 29, false, false⟩, ⟨_, parses, by decide +kernel⟩, by decide, rfl, rfl, rfl⟩,
    codeAt, fun _ h => nomatch h⟩

theorem gcd_code : CodeOf F (sel "gcd_u32") "gcd_u32" (region 0 37) :=
  ⟨rfl, ⟨⟨11, 4199280, 37, false, false⟩, ⟨_, parses, by decide +kernel⟩, by decide, rfl, rfl, rfl⟩,
    codeAt, fun _ h => nomatch h⟩

theorem bswap_code : CodeOf F (sel "bswap32_manual") "bswap32_manual" (region 0xb0 5) :=
  ⟨rfl, ⟨⟨9, 4199456, 5, false, false⟩, ⟨_, parses, by decide +kernel⟩, by decide, rfl, rfl, rfl⟩,
    codeAt, fun _ h => nomatch h⟩

theorem clamp_row : silmaril.elf.abi.leaf_arith.clamp_i32 :=
  ⟨clamp_code, clamp_conforms .total⟩

theorem sat_row : silmaril.elf.abi.leaf_arith.sat_add_u32 :=
  ⟨sat_code, sat_conforms .total⟩

theorem absent_all : ∀ e ∈ coverage.excluded,
    (match e.2 with
      | .absent _ => decide ((L.assemble bodies ld).select (sel e.1) = some none)
      | _ => true) = true := by
  decide +kernel

theorem absent {f why : String} (h : (f, Exclusion.absent why) ∈ coverage.excluded) :
    Lookup F (sel f) none :=
  ⟨_, parses, of_decide_eq_true (absent_all _ h)⟩

theorem header_row : silmaril.elf.abi.leaf_arith.arith_h := by
  refine ⟨coverage_check, fun _ _ h => absent h, fun f hf => ?_⟩
  simp only [coverage, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨_, rfl, clamp_row⟩
  · exact ⟨_, rfl, sat_row⟩

end Silmaril.Proofs.Elf.Abi.LeafArith

end
