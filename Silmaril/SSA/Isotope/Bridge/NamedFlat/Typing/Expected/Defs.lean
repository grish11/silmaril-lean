module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Defs

/-! # Check written injections and case operands -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open LetCase.LocallyNameless (Tm)

universe u v
variable {Base : Type u} {F : Type v} {labels : Nat} [DecidableEq Base] [HasTy F (Ty Base)]

/-- Infer an expression type, using the expected type to resolve missing
summands. Let initializers still have to synthesize their own types. -/
def inferAt : {n : Nat} → BoundCtx (Ty Base) n → Option (Ty Base) → Tm Empty F n → Option (Ty Base)
  | _, ctx, _, .bv i => some (ctx.get i)
  | _, _, _, .unit => some .unit
  | _, ctx, expected, .pair a b =>
    let (left, right) := match expected with
      | some (.product A B) => (some A, some B)
      | _ => (none, none)
    (inferAt ctx left a).bind fun A => (inferAt ctx right b).map (.product A)
  | _, ctx, _, .op f a =>
    if inferAt ctx (some (instrSrc f)) a = some (instrSrc f) then some (instrTrg f) else none
  | _, ctx, expected, .let₁ value body =>
    (inferAt ctx none value).bind fun A => inferAt (.snoc ctx A) expected body
  | _, ctx, expected, .let₂ value body => do
    let .product A B ← inferAt ctx none value | none
    inferAt (.snoc (.snoc ctx A) B) expected body
  | _, ctx, some (.coprod A B), .inl a =>
    if inferAt ctx (some A) a = some A then some (.coprod A B) else none
  | _, ctx, some (.coprod A B), .inr b =>
    if inferAt ctx (some B) b = some B then some (.coprod A B) else none
  | _, ctx, expected, .case test left right => do
    let .coprod A B ← inferAt ctx none test | none
    let C ← inferAt (.snoc ctx A) expected left
    if inferAt (.snoc ctx B) expected right = some C ∧ expected.getD C = C then some C else none
  | _, _, _, _ => none

def inferExpected {n : Nat} (ctx : BoundCtx (Ty Base) n) (expr : Tm Empty F n) : Option (Ty Base) :=
  inferAt ctx none expr

/-- Check each instruction and outgoing positional label against the supplied
capture and payload types. Case payload types come from the discriminant. -/
def checkBodyExpected (types : Fin labels → Ty Base) :
    {n : Nat} → BoundCtx (Ty Base) n → LambdaSSA.Flat F labels n → Bool
  | _, ctx, .br label arg => decide (inferAt ctx (some (types label)) arg = some (types label))
  | _, ctx, .let₁ op rest =>
      match inferExpected ctx op with
      | some A => checkBodyExpected types (.snoc ctx A) rest
      | none => false
  | _, ctx, .let₂ op rest =>
      match inferExpected ctx op with
      | some (.product A B) => checkBodyExpected types (.snoc (.snoc ctx A) B) rest
      | _ => false
  | _, ctx, .case op left right =>
      match inferExpected ctx op with
      | some (.coprod A B) => checkBodyExpected types (.snoc ctx A) left && checkBodyExpected types (.snoc ctx B) right
      | _ => false

/-- Check the entry's captures and the block and exit profiles. -/
def checkExpected {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base)
    (external : Fin exits → Ty Base) : Bool :=
  let types := SSA.FiniteSum.append internal external
  checkBodyExpected types captures graph.entry &&
    (List.finRange blocks).all fun i => checkBodyExpected types (.snoc captures (internal i)) (graph.block i)

end Silmaril.Isotope.Bridge.NamedFlat
