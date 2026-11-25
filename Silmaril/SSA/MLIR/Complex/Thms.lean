module

public import Silmaril.SSA.MLIR.Complex.Defs
import Silmaril.SSA.MLIR.Math.Binary64.Thms
import Silmaril.Proofs.SSA.MLIR.Complex.Create

public section

namespace Silmaril.MLIR.Complex

/-- Construction followed by the real projection returns the original real bits. -/
theorem re_create (r i : Math.Binary64) :
    Op.re.executable (Op.create.executable (r, i)) = r := rfl

/-- Construction followed by the imaginary projection returns the original imaginary bits. -/
theorem im_create (r i : Math.Binary64) :
    Op.im.executable (Op.create.executable (r, i)) = i := rfl

theorem reference_re_create (r i : ℝ) :
    (denote .re).reference.value ((denote .create).reference.value (r, i) trivial) trivial = r := rfl

theorem reference_im_create (r i : ℝ) :
    (denote .im).reference.value ((denote .create).reference.value (r, i) trivial) trivial = i := rfl

theorem conj_conj (z : complex.encoded) :
    Op.conj.executable (Op.conj.executable z) = z :=
  Prod.ext rfl (Math.Binary64.neg_neg z.2)

theorem reference_conj_conj (z : ℂ) :
    (denote .conj).reference.value ((denote .conj).reference.value z trivial) trivial = z :=
  star_star z

theorem conj_imaginary_positive_zero :
    (denote .conj).Executes (0x8000000000000000, 0) (0x8000000000000000, 0x8000000000000000) :=
  rfl

/-- Construction agrees with its reference whenever both components decode. -/
theorem create_realizes (decode : Math.Binary64 → Option ℝ) :
    (denote .create).RealizesOn (createObservation decode)
      (fun bits => ∃ parts, decodeParts decode bits = some parts) (denote .create).Executes :=
  Proofs.MLIR.Complex.create_realizes decode

end Silmaril.MLIR.Complex
