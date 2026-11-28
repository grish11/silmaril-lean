module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Compile.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Thms

/-! # A two-request program written as one step

`duoProgram l₁ l₂` is one written program: it sends the request `l₁`
with the state as query; on the left reply it sends the request `l₂`
with the first reply's payload as query and returns or repeats by the
second reply; on the right reply it repeats with the first payload.

`chainedStep p₁ p₂` is the same behaviour written as two steps: the step
of `p₁`, then a case on its packed result that feeds a return into the
step of `p₂` and keeps a repeat.

`StepFactors p p₁ p₂` says that the written step of `p` and the two
steps are equal in the quotient. It is a hypothesis of this file, not a
theorem.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)

variable {K : Nat}

/-- Two requests in one written program. -/
def duoProgram (l₁ l₂ : Bool) : Program :=
  .ask l₁ (.read 0) (.ask l₂ (.read 0) (.ret 0 0) (.ret 1 0)) (.ret 1 0)

theorem bitState_typed : ValueBranches [Bit] (.br 0 (.inl (.var 0)) : Region signature.Instr) [State] :=
  .br rfl (.inl (.var rfl))

theorem keep_typed :
    ValueBranches [State] (.br 0 (.inr (.var 0)) : Region signature.Instr) [Silmaril.coprod Bit State] :=
  .br rfl (.inr (.var rfl))

/-- After a first step: a returned Bit becomes the state of the step of
`p₂`, a repeat is kept. -/
def chainRegion (p₂ : Program) : Region signature.Instr :=
  .case (.var 0)
    (((Region.br 0 (.inl (.var 0))).lsubst
      (fun _ => (stepRegion p₂).renameVars (lift Nat.succ))).renameVars (lift Nat.succ))
    ((Region.br 0 (.inr (.var 0))).renameVars (lift Nat.succ))

theorem chain_typed (p₂ : Program) :
    ValueBranches [Silmaril.coprod Bit State] (chainRegion p₂) [Silmaril.coprod Bit State] :=
  caseValueBranches (seqValueBranches bitState_typed (step_typed p₂)) keep_typed

/-- The step of `p₁` followed by the chain into `p₂`. -/
def chainedStep (p₁ p₂ : Program) : Region signature.Instr :=
  (stepRegion p₁).lsubst (fun _ => (chainRegion p₂).renameVars (lift Nat.succ))

theorem chainedStep_typed (p₁ p₂ : Program) :
    ValueBranches [State] (chainedStep p₁ p₂) [Silmaril.coprod Bit State] :=
  seqValueBranches (step_typed p₁) (chain_typed p₂)

/-- The written step of `p` equals the step of `p₁` chained into `p₂`. -/
def StepFactors (p p₁ p₂ : Program) : Prop :=
  Eqv false [State] (stepRegion p) (chainedStep p₁ p₂) [Silmaril.coprod Bit State]

/-- The trees of the row `(p₁, p₂)` routed by `a`: a returned Bit sends
the request of `p₂` with that Bit as query, a repeat takes its action. -/
def duoKids (K : Nat) (p₂ : Program) (a : Bool → Bool → Act K) (x y : Bool) : Tree K :=
  match x with
  | false => .ask y p₂ fun x' y' => .leaf (a x' y')
  | true => .leaf (a true y)

/-- A router table all of whose rows are two-request programs. -/
def duoRouter (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K) : Router K :=
  ⟨fun i => duoProgram (l₁ i) (l₂ i), act⟩

/-- The same table written as literal request trees. -/
def duoSource (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K) : LTable K :=
  ⟨l₁, fun i x y =>
    match x with
    | false => .ask y (l₂ i) fun x' y' => .leaf (act i x' y')
    | true => .leaf (act i true y)⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
