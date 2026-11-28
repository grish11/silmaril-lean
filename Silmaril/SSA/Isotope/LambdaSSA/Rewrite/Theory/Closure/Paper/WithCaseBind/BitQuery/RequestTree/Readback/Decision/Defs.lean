module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Defs

/-! # Read a pure decision on live Bits before a request -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback

open Silmaril.DeBruijn (lift)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition (sameBody)

/-- Exact comparison of the selected signature's two request labels. -/
@[instance_reducible]
def requestDecEq : DecidableEq signature.Instr
  | .ask l, .ask r =>
    if h : l = r then .isTrue (congrArg Op.ask h)
    else .isFalse (fun e => h (Op.ask.inj e))

attribute [local instance] requestDecEq

def literalQuery : Tm signature.Instr → Option Bool
  | .inl .unit => some false
  | .inr .unit => some true
  | _ => none

structure Decision (n : Nat) where
  label : Bool
  query : Expr n
  left : Region signature.Instr
  right : Region signature.Instr

def Decision.region {n : Nat} (d : Decision n) : Region signature.Instr :=
  queryCase false d.label d.query (fun i => .var i) d.left d.right

/-- Find the first request and remove the intervening unit-binder positions
from its proposed continuations. Exact re-emission checks the weakening. -/
def requestArms (depth : Nat) : Region signature.Instr →
    Option (Bool × Region signature.Instr × Region signature.Instr)
  | .case (.var _) l _ => requestArms (depth + 1) l
  | .case (.op (.ask label) _) l r =>
    some (label, l.renameVars (lift (· - depth)), r.renameVars (lift (· - depth)))
  | _ => none

def leafQuery : Region signature.Instr → Option Bool
  | .case (.op (.ask _) arg) _ _ => literalQuery arg
  | _ => none

/-- A split tests the next slot in fixed order. A read may test any
remaining slot and goes directly to false and true requests. -/
def proposeQuery (depth : Nat) : (n : Nat) → Region signature.Instr → Option (Expr n)
  | n + 1, .case (.var j) l r =>
    if j = depth + depth then
      .split <$> proposeQuery (depth + 1) n l <*> proposeQuery (depth + 1) n r
    else if hi : depth + depth ≤ j ∧ j - (depth + depth) < n + 1 then
      if leafQuery l = some false ∧ leafQuery r = some true then
        some (.read ⟨j - (depth + depth), hi.2⟩)
      else none
    else none
  | _, raw => (leafQuery raw).map Expr.literal

/-- Every leaf must use the same request label and the same two
continuations, weakened through exactly its already written unit binders. -/
def readDecision (n : Nat) (raw : Region signature.Instr) : Option (Decision n) := do
  let (label, left, right) ← requestArms 0 raw
  let query ← proposeQuery 0 n raw
  let d : Decision n := ⟨label, query, left, right⟩
  if sameBody raw d.region then some d else none

def caseOperand (a : Tm signature.Instr) : Tm signature.Instr :=
  .case a (literal false) (literal true)

/-- The local missing beta comparison after focusing the operand's input.
The payload is the actual unit constructor payload in that branch.
Both endpoints perform the one request and have the same continuations. -/
def CaseOperandBetaIn
    (relation : VCtx (Ty Empty) → Region signature.Instr → Region signature.Instr → LCtx (Ty Empty) → Prop) :
    Prop :=
  ∀ {Γ L : List (Ty Empty)} (label b : Bool) {l r : Region signature.Instr},
    ValueBranches (Bit :: Ty.unit :: Γ) l L → ValueBranches (Bit :: Ty.unit :: Γ) r L →
      relation (Ty.unit :: Γ) (.case (.op (.ask label) (caseOperand (constructorBit b (.var 0)))) l r)
        (requestRegion label b l r) L

def CaseOperandBeta : Prop := CaseOperandBetaIn Paper.Eqv

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback
