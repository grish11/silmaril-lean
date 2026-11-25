module

public import Silmaril.SSA.MLIR.Math.Defs
import Silmaril.SSA.MLIR.Math.Binary64.Thms

public section

namespace Silmaril.MLIR.Math

open MathCollection

theorem absf_idempotent (x : Binary64) :
    Op.absf.executable.map (fun f => f (f x)) = Op.absf.executable.map (fun f => f x) :=
  congrArg some (Binary64.abs_abs x)

theorem reference_absf_idempotent (x : ℝ) :
    (denote .absf).reference.value ((denote .absf).reference.value x trivial) trivial =
      (denote .absf).reference.value x trivial := abs_abs x

theorem absf_negative_zero :
    (denote .absf).Executes 0x8000000000000000 0 := rfl

theorem absf_negative_nan :
    (denote .absf).Executes 0xfff8000000000042 0x7ff8000000000042 := rfl

theorem log_one : (denote .log).reference.Holds 1 0 := ⟨zero_lt_one, Real.log_one⟩

theorem log_zero_outside_domain : ¬ (denote .log).reference.domain 0 := lt_irrefl 0

theorem log_rejects_decoded_zero (obs : Observation scalar scalar) {input output : Binary64}
    (decoded : obs.decodeInput input = some 0) : ¬ (denote .log).Accepts obs input output := by
  rintro ⟨x, _, hx, ⟨inDomain, _⟩, _⟩
  have h : x = 0 := Option.some.inj (hx.symm.trans decoded)
  exact log_zero_outside_domain (h ▸ inDomain)

theorem log_no_local_evaluator : Op.log.executable = none := rfl

end Silmaril.MLIR.Math
