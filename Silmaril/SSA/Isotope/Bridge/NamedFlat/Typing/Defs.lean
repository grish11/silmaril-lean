module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Defs

/-! # Exact type checking for the named adapter's expression fragment -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open LetCase.LocallyNameless (Tm)

universe u v
variable {Base : Type u} {F : Type v} {labels : Nat} [DecidableEq Base] [HasTy F (Ty Base)]

/-- Synthesize a type for a variable, unit, product or fully typed primitive. -/
def infer : {n : Nat} → BoundCtx (Ty Base) n → Tm Empty F n → Option (Ty Base)
  | _, ctx, .bv i => some (ctx.get i)
  | _, _, .unit => some .unit
  | _, ctx, .pair a b => (infer ctx a).bind fun A => (infer ctx b).map (.product A)
  | _, ctx, .op f a =>
      if infer ctx a = some (instrSrc f) then some (instrTrg f) else none
  | _, _, _ => none

/-- Check each instruction and outgoing positional label against the supplied
capture and payload types. Case payload types come from the discriminant. -/
def checkBody (types : Fin labels → Ty Base) :
    {n : Nat} → BoundCtx (Ty Base) n → LambdaSSA.Flat F labels n → Bool
  | _, ctx, .br label arg => decide (infer ctx arg = some (types label))
  | _, ctx, .let₁ op rest =>
      match infer ctx op with
      | some A => checkBody types (.snoc ctx A) rest
      | none => false
  | _, ctx, .let₂ op rest =>
      match infer ctx op with
      | some (.product A B) => checkBody types (.snoc (.snoc ctx A) B) rest
      | _ => false
  | _, ctx, .case op left right =>
      match infer ctx op with
      | some (.coprod A B) => checkBody types (.snoc ctx A) left && checkBody types (.snoc ctx B) right
      | _ => false

/-- Check the entry's captures and the block and exit profiles. -/
def check {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base)
    (external : Fin exits → Ty Base) : Bool :=
  let types := SSA.FiniteSum.append internal external
  checkBody types captures graph.entry &&
    (List.finRange blocks).all fun i => checkBody types (.snoc captures (internal i)) (graph.block i)

end Silmaril.Isotope.Bridge.NamedFlat
