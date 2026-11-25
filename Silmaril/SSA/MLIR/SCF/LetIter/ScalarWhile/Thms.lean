module

public import Silmaril.SSA.MLIR.SCF.LetIter.ScalarWhile.Defs
import Silmaril.SSA.MLIR.SCF.LetIter.ScalarWhile.Comparison

/-! The externally visible observations of the typed scalar while agree
with both the native LetIter loop and the verified CF lowering. -/

public section

namespace Silmaril.MLIR.SCF.LetIter.ScalarWhile

open Arith (Width Env)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Institution.Observational (Observation)
open Silmaril.Isotope.LetIter.Semantics (Fault)

variable {Op : OpSignature} {Input Result : List Width}
variable (loop : While Op Input Result) (evalOp : Pure.Eval Op) (input : Env Input)

/-- Every native return has the scalar result profile, and finite scalar
execution and native return observations determine the same values. -/
theorem returns_iff (out : Value (Atom loop.State loop.Payload Result)) :
    Observation.ret () out () ∈ observe loop evalOp input ↔
      ∃ result, out = .atom (.result result) ∧ ∃ fuel, loop.run evalOp fuel input = some result :=
  returns_iff_proof loop evalOp input out

/-- Native divergence and absence of a return at every scalar budget agree. -/
theorem diverges_iff :
    Observation.diverge () ∈ observe loop evalOp input ↔ loop.Diverges evalOp input :=
  diverges_iff_proof loop evalOp input

/-- The admitted pure scalar instance yields no native fault observations. -/
theorem no_fault : Observation.fault () () ∉ observe loop evalOp input :=
  fun h => Fault.false h

/-- The verified control-flow lowering agrees with every native return. -/
theorem cf_returns_iff (out : Value (Atom loop.State loop.Payload Result)) :
    Observation.ret () out () ∈ observe loop evalOp input ↔
      ∃ result, out = .atom (.result result) ∧ ∃ fuel, loop.lower.run evalOp fuel input = some result :=
  (returns_iff loop evalOp input out).trans <|
    exists_congr fun result => Iff.and Iff.rfl (loop.lower_returns_iff evalOp input result).symm

/-- The two lowerings agree on divergence. -/
theorem cf_diverges_iff :
    Observation.diverge () ∈ observe loop evalOp input ↔ loop.lower.Diverges evalOp input :=
  (diverges_iff loop evalOp input).trans (loop.lower_diverges_iff evalOp input).symm

end Silmaril.MLIR.SCF.LetIter.ScalarWhile
