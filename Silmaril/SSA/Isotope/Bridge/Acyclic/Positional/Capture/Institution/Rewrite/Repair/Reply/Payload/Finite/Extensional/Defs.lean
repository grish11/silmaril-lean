module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Defs

/-! # Assignment-indexed normal forms of witnessed binary programs -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional

open Isotope.LetCase.LocallyNameless (Tm)
open Kleisli (value)
open LambdaSSA (At)
open LambdaSSA.Acyclic (FiniteExit Operand)
open LambdaSSA.Acyclic.Positional.Capture.Reverse (Program)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)

local notation "U" => (Ty.unit : Sorts)

/-- The computation remaining at one retained assignment. Requests retain a
separate path for each combination of reply tag and payload. -/
inductive Path (L : List Sorts) where
  | ret (position : Position L) (result : Bool)
  | emit (label : Bool) (next : Path L)
  | request (label : Bool) (leftFalse leftTrue rightFalse rightTrue : Path L)

def Path.traceTree {L : List Sorts} : Path L → Reply.Normal (Exits.Exit L)
  | .ret p b => .ret (p.result b)
  | .emit b next => .emit b next.traceTree
  | .request req lf lt rf rt =>
    requestTree req (fun b => if b then lt.traceTree else lf.traceTree)
      (fun b => if b then rt.traceTree else rf.traceTree)

def Path.operand {L : List Sorts} (p : Path L) {k : Nat} (β : BoundCtx Sorts k) :
    Operand signature.Instr β (packedExitType L) :=
  match p with
  | .ret pos b => FiniteExit.tag L pos.1 pos.typed (bitOperand β b)
  | .emit b p =>
    let next := p.operand (β.snoc U)
    ⟨.let₁ (.op (.emit b) .unit) next.1, .let₁ (.op .unit) next.2⟩
  | .request req lf lt rf rt =>
    let ctx := (β.snoc Bit).snoc U
    let l₀ := lf.operand ctx
    let l₁ := lt.operand ctx
    let r₀ := rf.operand ctx
    let r₁ := rt.operand ctx
    requestOperand req false
      ⟨.case (.bv 0) l₀.1 l₁.1, .case .bv l₀.2 l₁.2⟩
      ⟨.case (.bv 0) r₀.1 r₁.1, .case .bv r₀.2 r₁.2⟩

def specialize {L : List Sorts} {n : Nat} (t : Normal L n) (env : Assignment n) : Path L :=
  match t with
  | .ret pos table => .ret pos (table env)
  | .emit b next => .emit b (specialize next env)
  | .request req l r =>
    .request req (specialize l (env.push false)) (specialize l (env.push true))
      (specialize r (env.push false)) (specialize r (env.push true))
  | .testRequest test low lf lr hf hr =>
    let rest := env.without test
    if env test then
      .request (!low) (specialize hf (rest.push false)) (specialize hf (rest.push true))
        (specialize hr (rest.push false)) (specialize hr (rest.push true))
    else
      .request low (specialize lf (rest.push false)) (specialize lf (rest.push true))
        (specialize lr (rest.push false)) (specialize lr (rest.push true))

/-- The common request's tested slot is an argument of normalization, not a
field of the normal form. -/
def commonNormal {L : List Sorts} {n : Nat} (t : CommonRequest.NormalSource L n)
    (test : Fin (n + 1)) (env : Assignment (n + 1)) : Path L :=
  let rest := env.without test
  if env test then
    .request t.request (specialize t.arms.trueLeft (rest.push false))
      (specialize t.arms.trueLeft (rest.push true)) (specialize t.arms.trueRight (rest.push false))
      (specialize t.arms.trueRight (rest.push true))
  else
    .request t.request (specialize t.arms.falseLeft (rest.push false))
      (specialize t.arms.falseLeft (rest.push true)) (specialize t.arms.falseRight (rest.push false))
      (specialize t.arms.falseRight (rest.push true))

/-- Use the existing native operands, including either placement of a common
request. In an equation each source can choose its own tested slot. -/
inductive Source (L : List Sorts) : Nat → Type where
  | tree {n : Nat} (p : Tree L n) : Source L n
  | common {n : Nat} (test : Fin (n + 1)) (p : CommonRequest.Source L n) : Source L (n + 1)

def Source.normal {L : List Sorts} {n : Nat} (p : Source L n) : Assignment n → Path L :=
  match p with
  | .tree t => specialize t.normal
  | .common test t => commonNormal t.normal test

def Source.operand {L : List Sorts} {n k : Nat} {β : BoundCtx Sorts k}
    (p : Source L n) (slots : Retained β n) : Operand signature.Instr β (packedExitType L) :=
  match p with
  | .tree t => t.operand slots
  | .common test t => t.operand slots test

def program (H : Sorts) (L : List Sorts) {n : Nat} (p : Source (H :: L) n) :
    Program signature.Instr (CommonRequest.bitCtx n) (H :: L) :=
  ⟨packedExitType (H :: L), p.operand (CommonRequest.bitSlots n),
    Exits.router (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))⟩

def equation (H : Sorts) (L : List Sorts) {n : Nat} (p q : Source (H :: L) n) :
    GrammarEquation signature :=
  ⟨⟨n, CommonRequest.bitCtx n, H :: L⟩, program H L p, program H L q⟩

noncomputable def programOutcomes (H : Sorts) (L : List Sorts) {n : Nat}
    (p : Source (H :: L) n) (env : Assignment n) :
    Set (Outcome (value (packedExitType (H :: L)))) :=
  (Kleisli.run model (program H L p).toLetCase.2 (boundEnv value (CommonRequest.packedAssignment n env))).outcomes

def literalSubst {n k : Nat} (β : BoundCtx Sorts k) (env : Assignment n) :
    Fin n → Tm Empty signature.Instr k :=
  fun i => (bitOperand β (env i)).1

def assignmentMatches {k m n : Nat} {β : BoundCtx Sorts k} (γ : BoundCtx Sorts m)
    (slots : Retained β n) (σ : Fin k → Tm Empty signature.Instr m) (env : Assignment n) : Prop :=
  ∀ i, σ (slots i).1 = literalSubst γ env i

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional
