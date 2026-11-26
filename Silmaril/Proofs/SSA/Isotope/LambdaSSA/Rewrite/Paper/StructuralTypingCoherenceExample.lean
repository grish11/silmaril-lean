module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Iteration.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Thms

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Extension.Singleton
open Extension.Singleton.StructuralValues

private inductive Op where
  | poll

private abbrev U : Ty Empty := .unit
private abbrev Flag : Ty Empty := .coprod U U

instance : HasTy Op (Ty Empty) where
  src _ := U
  trg _ := Flag

instance : HasEff Op Bool := ⟨fun _ => true⟩

private def entry : Region Op := .br 0 .unit
private def blocks (_ : Fin 1) : Region Op :=
  .case (.op .poll (.var 0)) (.br 0 (.var 0)) (.br 1 (.var 0))

private def loop : Region Op := .cfg entry 1 blocks

private theorem loopTyped : loop.HasType [U] [U] :=
  .cfg (fun _ => U) (.br rfl .unit)
    (fun _ => .case (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl)))

/-- The entry's unit payload fixes the feedback state, and the request
signature fixes both case arm contexts. -/
private theorem loopDetermined : DeterminedRegion [U] loop [U] := by
  refine .cfg (R := fun _ => U) ?_ (.br rfl .unit) fun _ =>
    .case ?_ (.op (.var rfl)) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  · intro S h _
    cases h with
    | br atLabel term =>
        cases term
        have h0 : S 0 = U := Option.some.inj (by simpa [At] using atLabel)
        funext i
        exact Fin.cases h0 (fun j => Fin.elim0 j) i
  · intro D h
    cases h
    rfl

local notation "Seed" => WithCaseReturns.BinaryFold.JoinedStep (τ := Ty Empty) (Φ := Op) true
local notation "inc" => inclusion Seed

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric
  computationDistributive valueDistributive guardedIteration guardedElgot
attribute [local instance] Extension.Singleton.StructuralValues.hasFiniteCoproducts

example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∀ {f}, RegionDenotes inc (typeModel Seed) loopTyped f →
      f = denoteRegion inc (typeModel Seed) loopTyped :=
  chosen_denoteRegion_eq Seed uniform loopDetermined loopTyped

local notation "CaseSeed" => WithCaseReturns.JoinedStep (τ := Ty Empty) (Φ := Op) true

/-- The case-return specialization uses the already-installed adapter. -/
example (uniform : WithCaseReturns.StructuralValues.StructuralUniformity (τ := Ty Empty) (Φ := Op) true) :
    letI := WithCaseReturns.StructuralValues.strongElgotOfUniformity true uniform
    letI := WithCaseReturns.StructuralValues.instructions (τ := Ty Empty) (Φ := Op) true
    ∀ {f}, RegionDenotes (inclusion CaseSeed) (typeModel CaseSeed) loopTyped f →
      f = denoteRegion (inclusion CaseSeed) (typeModel CaseSeed) loopTyped := by
  let strong := WithCaseReturns.StructuralValues.strongElgotOfUniformity true uniform
  let instr := WithCaseReturns.StructuralValues.instructions (τ := Ty Empty) (Φ := Op) true
  intro f d
  exact loopDetermined.eq_denoteRegion (inclusion CaseSeed) (typeModel CaseSeed) d

private def direct (_ : Fin 1) : Region Op := .br 0 (.var 0)
private def outward : Region Op := .cfg (.br 1 .unit) 1 direct

private theorem outwardTyped (A : Ty Empty) : outward.HasType [U] [U] :=
  .cfg (fun _ => A) (.br rfl .unit) (fun _ => .br rfl (.var rfl))

/-- The fixed outward interface does not recover the hidden table types. -/
example : ¬ LabelsDetermined [U] [U] (.br 1 (Tm.unit : Tm Op)) direct (fun _ => U) := by
  intro unique
  have labels := unique (fun _ => .empty) (.br rfl .unit) (fun _ => .br rfl (.var rfl))
  have impossible := congrFun labels 0
  cases impossible

/-- Both graph witnesses evaluate the same outward payload even if their
hidden block types were chosen differently. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    letI := strongElgotCentralUnit Seed uniform
    ∀ {f g}, RegionDenotes inc (typeModel Seed) (outwardTyped U) f →
      RegionDenotes inc (typeModel Seed) (outwardTyped .empty) g → f = g := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  let central := strongElgotCentralUnit Seed uniform
  intro f g d e
  obtain ⟨_, _, da, rfl⟩ := d.cfg_outward_branch inc (typeModel Seed) (rfl : At [U] 0 U)
  obtain ⟨_, _, ea, rfl⟩ := e.cfg_outward_branch inc (typeModel Seed) (rfl : At [U] 0 U)
  rw [DeterminedTerm.denotes_eq inc (typeModel Seed) .unit da ea]

private def reachedBlock (_ : Fin 1) : Region Op := .br 1 .unit

/-- A jump into the CFG can also leave a block's exact state type
undetermined. The unused arm of the injected payload can have either type. -/
example : ¬ LabelsDetermined [U] [U] (.br 0 (.inl (Tm.unit : Tm Op))) reachedBlock (fun _ => Flag) := by
  intro unique
  have labels := unique (fun _ => .coprod U .empty) (.br rfl (.inl .unit)) (fun _ => .br rfl .unit)
  have impossible := congrFun labels 0
  cases impossible

end Silmaril.Isotope.LambdaSSA.Region.Paper
