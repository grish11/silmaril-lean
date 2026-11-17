module

public import Silmaril.Proofs.Elf.Abi.Libm.Common
public import Silmaril.Machine.Abi.Conformance.Import.Thms
public import Silmaril.Machine.Abi.Conformance.Sse.Lrint.Thms
public import Silmaril.Data.Layout.Header.Import.Pinned.GlibcMath.Thms

/-! # glibc `libm.so.6` rows: the file facts and the proved rows

Each file fact is a kernel read of the file's kernel bytes or a computation on its parse `A0`;
the declarations are checked against the pinned `math.h` import; `lrint` and `llrint` conform at
every load base by `Conformance.Sse.Lrint.conforms`. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.Libm

open Silmaril.Elf Silmaril.Elf.Abi Silmaril.Elf.Abi.Libm
open Silmaril.Elf.Staged.Pinned.GlibcLibm236 (K ph0 ph1 ph2 ph3)
open Silmaril.Elf.Staged.Reader (codeAt_of_kbytes)
open Silmaril.Machine.Abi.Conformance
open Silmaril.Data.Layout.Header.Import.Pinned

/-! ## The file -/

theorem image_eq :
    image = A0.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize) := by
  decide +kernel

theorem loads_eq : A0.loads = [ph0, ph1, ph2, ph3] := by decide +kernel

/-- The file is x86-64, and 21 of its dynamic relocations are `R_X86_64_IRELATIVE`. -/
theorem irelative : A0.header.machine = EM_X86_64 ∧
    ((A0.relocs .dynamic).filter (·.kind == 37)).length = 21 ∧
    (A0.relocs .dynamic).any (·.kind == 37) = true := by
  decide +kernel

theorem not_untouched (c : Code) : ¬ Untouched F c :=
  not_untouched_of_irelative irelative.2.2 c

/-- The file is `ET_DYN` and admits the load base `0`. -/
theorem placement_zero : Placement F 0 :=
  ⟨_, parses, .inr ⟨by decide +kernel, rfl⟩, fun ph h => by revert ph; decide +kernel⟩

/-- The bounds a load base gives: every `PT_LOAD` ends below `2^47`. -/
theorem bounds {base : Nat} (h : Placement F base) :
    base + 62912 ≤ 2 ^ 47 ∧ base + 65536 + 472033 ≤ 2 ^ 47 ∧ base + 540672 + 367252 ≤ 2 ^ 47 ∧
      base + 912696 + 984 ≤ 2 ^ 47 := by
  obtain ⟨A, hA, -, hl⟩ := h
  cases parse_eq hA
  rw [loads_eq] at hl
  exact ⟨(hl ph0 (by simp)).2, (hl ph1 (by simp)).2, (hl ph2 (by simp)).2, (hl ph3 (by simp)).2⟩

theorem toNat_ofNat_add {v b : Nat} (h : v + b < 2 ^ 64) :
    (BitVec.ofNat 64 v + BitVec.ofNat 64 b).toNat = v + b := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : v < 2 ^ 64), Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]
  exact Nat.mod_eq_of_lt h

/-- The rebased image ends below `2^47` at every load base. -/
theorem image_bounds {base : Nat} (h : Placement F base) :
    ∀ r ∈ image.map (fun r => (r.1 + BitVec.ofNat 64 base, r.2)), r.1.toNat + r.2 ≤ 2 ^ 47 := by
  obtain ⟨h0, h1, h2, h3⟩ := bounds h
  intro r hr
  simp only [image, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · show (BitVec.ofNat 64 0 + BitVec.ofNat 64 base).toNat + 62912 ≤ _
    rw [toNat_ofNat_add (by omega)]; omega
  · show (BitVec.ofNat 64 65536 + BitVec.ofNat 64 base).toNat + 472033 ≤ _
    rw [toNat_ofNat_add (by omega)]; omega
  · show (BitVec.ofNat 64 540672 + BitVec.ofNat 64 base).toNat + 367252 ≤ _
    rw [toNat_ofNat_add (by omega)]; omega
  · show (BitVec.ofNat 64 912696 + BitVec.ofNat 64 base).toNat + 984 ≤ _
    rw [toNat_ofNat_add (by omega)]; omega

/-! ## Code -/

/-- `CodeOf` of a row: the versioned lookup of `GLIBC_2.2.5` finds `.dynsym` entry `i` at the
code's value and size, the entry is an `STT_FUNC` named `f`, and the R+X `PT_LOAD` holds the
bytes. -/
theorem rowCodeOf {f : String} {value : Nat} {bytes : List Silmaril.X86.Byte} (i : Nat)
    (hv : value < 2 ^ 64)
    (hl : A0.select ((Binding.dynsym (some v2_2_5)).sel f) =
      some (some ⟨i, value, bytes.length, false, false⟩))
    (hs : funcSymB A0 i f = true)
    (hc : Silmaril.Elf.Staged.Reader.kread K
        (ph1.offset + (value - ph1.virtualAddress)) bytes.length =
      some (Silmaril.X86.Link.Blob.valueLE bytes))
    (hf : A0.phdrs.find? (codeSeg value bytes.length) = some ph1) :
    CodeOf F (.dynsym (some v2_2_5)) f (codeAt value bytes) := by
  have hvv : (BitVec.ofNat 64 value).toNat = value := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  refine codeOf _ f _ i rfl ?_ hs ?_ (fun _ h => nomatch h) image_eq
  · show A0.select _ = some (some ⟨i, (BitVec.ofNat 64 value).toNat + 0, bytes.length, false, false⟩)
    rw [hvv]; exact hl
  · show CodeAt F (BitVec.ofNat 64 value).toNat bytes
    rw [hvv]
    exact codeAt_of_kbytes K.wf_true K.toByteArray_eq parses hf hc

theorem lrint_code : CodeOf F (.dynsym (some v2_2_5)) "lrint" lrintCode :=
  rowCodeOf 1135 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem llrint_code : CodeOf F (.dynsym (some v2_2_5)) "llrint" llrintCode :=
  rowCodeOf 1119 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem lrintf_code : CodeOf F (.dynsym (some v2_2_5)) "lrintf" lrintfCode :=
  rowCodeOf 808 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem llrintf_code : CodeOf F (.dynsym (some v2_2_5)) "llrintf" llrintfCode :=
  rowCodeOf 957 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem round_code : CodeOf F (.dynsym (some v2_2_5)) "round" roundCode :=
  rowCodeOf 107 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem fmax_code : CodeOf F (.dynsym (some v2_2_5)) "fmax" fmaxCode :=
  rowCodeOf 578 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem fmin_code : CodeOf F (.dynsym (some v2_2_5)) "fmin" fminCode :=
  rowCodeOf 877 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem fpclassify_code : CodeOf F (.dynsym (some v2_2_5)) "__fpclassify" fpclassifyCode :=
  rowCodeOf 810 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem signbit_code : CodeOf F (.dynsym (some v2_2_5)) "__signbit" signbitCode :=
  rowCodeOf 208 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem finiteInternal_code : CodeOf F (.dynsym (some v2_2_5)) "__finite" finiteInternalCode :=
  rowCodeOf 382 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem finite_code : CodeOf F (.dynsym (some v2_2_5)) "finite" finiteCode :=
  rowCodeOf 199 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! ## Declarations -/

/-- Every row function's prototype in `hdr` is the pinned import's, in a System V convention. -/
theorem hdr_agrees : rowNames.all (fun f => hdr.proto? f == glibcMath.proto? f &&
    (glibcMath.fn? f).any (fun x => sysvCcs.contains x.2.cc)) = true := by
  rw [import_glibcMath]; decide +kernel

theorem hdr_env : hdr.env = glibcMath.header.env := by
  have h1 : hdr.env = [] := by decide +kernel
  have h2 : glibcMath.header.env = [] := by rw [import_glibcMath]; decide +kernel
  rw [h1, h2]

theorem declares_iff : ∀ f ∈ rowNames, ∀ p : abi.V.Proto,
    Declares abi hdr f p ↔ DeclaresImport abi sysvCcs glibcMath f p :=
  declares_iff_of_all hdr_agrees fun cp => by rw [hdr_env]

/-- `Declares` from the header's prototype and its lowering. -/
theorem declares_of {f : String} {p : Silmaril.Machine.Abi.SystemV.Scalar.Proto}
    (h : (hdr.proto? f).bind (fun cp =>
      (lowerScalar Silmaril.Data.Layout.sysvX86_64 hdr.env cp).toOption) = some p) :
    Declares abi hdr f p := by
  cases hp : hdr.proto? f with
  | none => rw [hp] at h; cases h
  | some cp =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    cases hl : lowerScalar Silmaril.Data.Layout.sysvX86_64 hdr.env cp with
    | error e => rw [hl] at h; cases h
    | ok q =>
      rw [hl] at h
      cases (Option.some.inj h : q = p)
      exact ⟨cp, hp, hl⟩

theorem lrint_declared : Declares abi hdr "lrint" Silmaril.Machine.Abi.Conformance.Sse.Lrint.proto :=
  declares_of (by decide +kernel)
theorem llrint_declared :
    Declares abi hdr "llrint" Silmaril.Machine.Abi.Conformance.Sse.Lrint.proto :=
  declares_of (by decide +kernel)
theorem lrintf_declared : Declares abi hdr "lrintf" fLong := declares_of (by decide +kernel)
theorem llrintf_declared : Declares abi hdr "llrintf" fLong := declares_of (by decide +kernel)
theorem round_declared : Declares abi hdr "round" dDouble := declares_of (by decide +kernel)
theorem fmax_declared : Declares abi hdr "fmax" ddDouble := declares_of (by decide +kernel)
theorem fmin_declared : Declares abi hdr "fmin" ddDouble := declares_of (by decide +kernel)
theorem fpclassify_declared : Declares abi hdr "__fpclassify" dInt := declares_of (by decide +kernel)
theorem signbit_declared : Declares abi hdr "__signbit" dInt := declares_of (by decide +kernel)
theorem finiteInternal_declared : Declares abi hdr "__finite" dInt := declares_of (by decide +kernel)
theorem finite_declared : Declares abi hdr "finite" dInt := declares_of (by decide +kernel)

/-! ## `lrint` and `llrint` -/

theorem lrint_rebase (base : Nat) : lrintCode.rebase base =
    Silmaril.Machine.Abi.Conformance.Sse.Lrint.code (BitVec.ofNat 64 0x32760 + BitVec.ofNat 64 base)
      (image.map fun r => (r.1 + BitVec.ofNat 64 base, r.2)) := rfl

theorem llrint_rebase (base : Nat) : llrintCode.rebase base =
    Silmaril.Machine.Abi.Conformance.Sse.Lrint.code (BitVec.ofNat 64 0x32760 + BitVec.ofNat 64 base)
      (image.map fun r => (r.1 + BitVec.ofNat 64 base, r.2)) := rfl

theorem code_bound {base : Nat} (h : Placement F base) :
    (BitVec.ofNat 64 0x32760 + BitVec.ofNat 64 base).toNat + 6 ≤ 2 ^ 47 := by
  obtain ⟨-, h1, -⟩ := bounds h
  rw [toNat_ofNat_add (by omega)]; omega

theorem lrint_conforms : ∀ base, Placement F base →
    Conforms abi mach .total hdr "lrint" Silmaril.Machine.Abi.Conformance.Sse.Lrint.proto
      (lrintCode.rebase base) 0 Silmaril.Machine.Abi.Conformance.Sse.Lrint.spec := by
  intro base h
  rw [lrint_rebase]
  exact Silmaril.Machine.Abi.Conformance.Sse.Lrint.conforms lrint_declared (code_bound h)
    (image_bounds h)

theorem llrint_conforms : ∀ base, Placement F base →
    Conforms abi mach .total hdr "llrint" Silmaril.Machine.Abi.Conformance.Sse.Lrint.proto
      (llrintCode.rebase base) 0 Silmaril.Machine.Abi.Conformance.Sse.Lrint.spec := by
  intro base h
  rw [llrint_rebase]
  exact Silmaril.Machine.Abi.Conformance.Sse.Lrint.conforms llrint_declared (code_bound h)
    (image_bounds h)

end Silmaril.Proofs.Elf.Abi.Libm

end
