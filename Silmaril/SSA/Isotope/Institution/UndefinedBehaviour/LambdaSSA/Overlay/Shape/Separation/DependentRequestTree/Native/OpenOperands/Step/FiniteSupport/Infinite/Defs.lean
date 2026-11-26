module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Defs

/-! # Typed infinite replay against a recorded finite query table -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open Syntax (Payload StatePrimitives)

universe u v w

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty}
  {σ : Type v} {τ : Type w}

/-- A typed view of an infinite path in the guarded native feedback graph. -/
structure GuardedReplay (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (p : Packet R) (s : σ) where
  point : Nat → Packet R × σ
  start : point 0 = (p, s)
  step : ∀ n, (g.head caller (point n).1).execute prim (point n).2 =
    .repeat (point (n + 1)).1 (point (n + 1)).2

namespace GuardedReplay

variable {g : Table S R} {caller : Payload (R.get g.entry)} {prim : StatePrimitives Φ σ}
  {p : Packet R} {s : σ}

/-- Match the complete typed query key. The answer is unconstrained here. -/
def listed (run : GuardedReplay g caller prim p s) (rows : List (RunRow Φ σ)) (i : Nat) : Prop :=
  match g.head caller (run.point i).1 with
  | .exit .. => False
  | .request f a _ => ∃ reply, (⟨f, a, (run.point i).2, reply⟩ : RunRow Φ σ) ∈ rows

def mappedStep (run : GuardedReplay g caller prim p s) (code : σ → τ)
    (other : StatePrimitives Φ τ) (i : Nat) : Prop :=
  (g.head caller (run.point i).1).execute other (code (run.point i).2) =
    .repeat (run.point (i + 1)).1 (code (run.point (i + 1)).2)

/-- Either stop at the first unlisted key or replay every step in the
recorded table. The reached stores in both cases are in the finite support. -/
inductive Treatment [DecidableEq σ] (run : GuardedReplay g caller prim p s) (rows : List (RunRow Φ σ))
    (support : RunSupport σ s) (other : Syntax.Primitives Φ support.values.length) : Prop where
  | truncate (cut : Nat) (earlier : ∀ i < cut, run.listed rows i ∧ run.mappedStep support.code other i)
      (absent : ¬ run.listed rows cut) (covered : ∀ i ≤ cut, (run.point i).2 ∈ support.values)
      (stop : (g.head caller (run.point cut).1).execute other (support.code (run.point cut).2) = .diverge)
  | retain (listed : ∀ i, run.listed rows i) (covered : ∀ i, (run.point i).2 ∈ support.values)
      (steps : ∀ i, run.mappedStep support.code other i)

end GuardedReplay
end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
