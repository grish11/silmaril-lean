module

public import Silmaril.SSA.MLIR.SCF.LetIter.Thms
public import Silmaril.SSA.MLIR.SCF.LetIter.ScalarWhile.Partial

/-! # The single-exit LambdaSSA bridge

The region view lowers to native LetIter, then uses the repository's
single-exit compiler. The compiler tags returns with exit zero and preserves
faults and divergence. The scalar specialization uses the independently
defined typed while evaluator and its partial iteration.
-/

@[expose] public section

universe u v w

namespace Silmaril.MLIR.SCF.LetIter

open Silmaril.Isotope
open Silmaril.Isotope.Morphism
open Silmaril.Isotope.Institution.Observational (Model Observation iterSSA lambdaSSA ssaBeh ssaBeh_compileSingle)
open Silmaril.Logic.Institution (Inst)

variable {Φ : Type u} {n : Nat}

/-- Use the native compiler on the region view's LetIter program. -/
def RegionLoop.compile (p : RegionLoop Φ n) : SSAIter.ScopedRegion Φ 1 n :=
  ⟨SSAIter.compileSingle p.lower, SSAIter.compileSingle_scoped p.lower⟩

/-- Compilation preserves and reflects returns, faults and divergence at
each ambient model. Only finite answers acquire the single exit label. -/
theorem RegionLoop.ssaBeh_compile (p : RegionLoop Φ n) (M : Model.{u, v, w} Φ n) :
    ssaBeh 1 M p.compile = Observation.mapValue (fun value => ((0 : Nat), value)) '' p.observe M := by
  rw [RegionLoop.compile, ssaBeh_compileSingle, p.observe_eq_iterBeh]

/-- Compose the region-view and native single-exit compiler comorphisms
over the discrete category of scopes. -/
def lowerLambdaSSA : Inst.CoHom (regionBehaviour.{u, v, w} Φ).inst (lambdaSSA.{u, v, w} Φ 1).inst :=
  lowerDiscrete.{u, v, w}.comp (iterSSA.{u, v, w} Φ).coHom

namespace ScalarWhile

open Arith (Width Env)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Input Result : List Width}
variable (loop : While Op Input Result) (evalOp : Pure.Eval Op) (input : Env Input)

/-- Compile the independently typed scalar while using the native compiler. -/
def toLambdaSSA : SSAIter.ScopedRegion (Call Op Input Result loop.State loop.Payload) 1 0 :=
  (toRegionLoop loop).compile

/-- The native compiler preserves the scalar result interface at its sole exit. -/
theorem toLambdaSSA_hasType :
    LambdaSSA.Region.HasType [] (toLambdaSSA loop).val [Ty.base Interface.result] :=
  SSAIter.compileSingle_hasType (toRegionLoop_wellTyped loop).lower

/-- Observations of the actual single-exit LambdaSSA region. -/
def observeLambdaSSA : Set (Observation (Nat × Value (Atom loop.State loop.Payload Result)) Unit) :=
  ssaBeh 1 (model evalOp input) (toLambdaSSA loop)

theorem observeLambdaSSA_eq :
    observeLambdaSSA loop evalOp input =
      Observation.mapValue (fun value => ((0 : Nat), value)) '' observe loop evalOp input :=
  ssaBeh_compileSingle (model evalOp input) (toRegionLoop loop).lower

/-- Every return is at exit zero and realizes a finite result of the scalar
iteration in Part, and every such result has a LambdaSSA return. -/
theorem lambdaSSA_returns_iff (label : Nat) (out : Value (Atom loop.State loop.Payload Result)) :
    Observation.ret () (label, out) () ∈ observeLambdaSSA loop evalOp input ↔
      label = 0 ∧ ∃ result, out = .atom (.result result) ∧ result ∈ denotePart loop evalOp input := by
  rw [observeLambdaSSA_eq, Observation.ret_mem_image_iff]
  constructor
  · rintro ⟨value, tag, ret⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj tag
    obtain ⟨result, rfl, run⟩ := (returns_iff loop evalOp input value).mp ret
    exact ⟨rfl, result, rfl, (mem_denotePart_iff loop evalOp input result).mpr run⟩
  · rintro ⟨rfl, result, rfl, ret⟩
    exact ⟨_, rfl, (returns_iff loop evalOp input _).mpr
      ⟨result, rfl, (mem_denotePart_iff loop evalOp input result).mp ret⟩⟩

/-- Divergence of the compiled region agrees with scalar divergence. -/
theorem lambdaSSA_diverges_iff :
    Observation.diverge () ∈ observeLambdaSSA loop evalOp input ↔ loop.Diverges evalOp input := by
  rw [observeLambdaSSA_eq, Observation.diverge_mem_image_iff, diverges_iff]

/-- For the pure scalar adapter, divergence is exactly undefinedness in Part. -/
theorem lambdaSSA_diverges_iff_denotePart_eq_none :
    Observation.diverge () ∈ observeLambdaSSA loop evalOp input ↔ denotePart loop evalOp input = Part.none :=
  (lambdaSSA_diverges_iff loop evalOp input).trans (denotePart_eq_none_iff loop evalOp input).symm

/-- Compiling the pure scalar instance introduces no native fault observation. -/
theorem lambdaSSA_no_fault :
    Observation.fault () () ∉ observeLambdaSSA loop evalOp input := by
  rw [observeLambdaSSA_eq, Observation.fault_mem_image_iff]
  exact no_fault loop evalOp input

end ScalarWhile
end Silmaril.MLIR.SCF.LetIter
