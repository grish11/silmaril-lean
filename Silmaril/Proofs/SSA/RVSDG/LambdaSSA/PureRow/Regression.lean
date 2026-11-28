module

import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Thms
meta import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Defs
meta import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Check.Defs
meta import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Defs
meta import Silmaril.SSA.Isotope.Types.Defs
public import Silmaril.SSA.RVSDG.Defs

namespace Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Regression

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open OrderedTheta (point)
open NestedTheta.Partial.Executable (Actions run)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev Ty := Silmaril.Ty Unit
private abbrev number : Ty := .base ()
deriving instance DecidableEq for PortType

@[reducible] private def Value : Ty → Type
  | .base _ => Nat
  | .product a b => Value a × Value b
  | .unit => PUnit
  | .coprod a b => Value a ⊕ Value b
  | .empty => PEmpty

private def coerceValue {A B : Ty} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => coerceValue g ∘ coerceValue f
  | .product f g => fun (a,b) => (coerceValue f a, coerceValue g b)
  | .coprod f g => Sum.map (coerceValue f) (coerceValue g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Ty where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => PEmpty.elim x, fun x => Empty.elim x⟩
  coe := coerceValue

private inductive Instr | addSeven | advance
  deriving DecidableEq

local instance : HasTy Instr Ty := ⟨fun _ => number, fun _ => number⟩
local instance : HasEff Instr Bool := ⟨fun | .addSeven => false | .advance => true⟩

private def effect : Instr → Nat → Nat → Option (Nat × Nat)
  | .addSeven, x, token => some (x + 7, token)
  | .advance, x, token =>
    if x = 99 then none else some (x + token, 10 * token + x)

private abbrev Runtime := StateT Nat Part

local instance : InstructionModel Instr Ty Bool Runtime where
  denote op x := StateT.mk fun token => Part.ofOption (effect op x token)
  denotePure
    | .addSeven, _, x => (show Nat from x) + 7
    | .advance, h, _ => by cases h
  denote_pure
    | .addSeven, _, _ => rfl
    | .advance, h, _ => by cases h

private def s : Segment Instr Bool number number number number :=
  ⟨⟨.addSeven, rfl, rfl⟩, rfl, ⟨.advance, rfl, rfl⟩, ⟨.advance, rfl, rfl⟩⟩

private def actions : Actions (model (τ := Ty) (Φ := Instr) (ε := Bool) (σ := Nat)) where
  primitive
    | .pure p h, .cons x .nil => some (.cons (pureCall (σ := Nat) p h x) .nil)
    | .ordered ⟨p, rfl, rfl⟩, .cons x (.cons token .nil) =>
      (effect p x token).map fun (y,next) => point (A := number) y next
  agrees
    | .pure _ _, .cons _ .nil => rfl
    | .ordered ⟨p, rfl, rfl⟩, .cons x (.cons token .nil) => by
      change Part.ofOption ((effect p x token).map (fun (y,next) => point (A := number) y next)) =
        Part.map (fun (y,next) => point (A := number) y next)
          ((Part.ofOption (effect p x token)).bind fun y => Part.some (y.1,y.2))
      cases effect p x token <;> simp [Part.ofOption]

private def swapRows (a b : Nat) : NestedTheta.Isomorphism.Mapping :=
  let swap n := if n = a then b else if n = b then a else n
  fun _ => ⟨swap, swap⟩

private def checkedMap (a b : Nat)
    {ps qs : List (Ports (OrderedRuntime.Structured.Ty Ty))}
    (left : NestedTheta.Graph (Op Instr Bool) (Wire number) [] ps (Output number number))
    (right : NestedTheta.Graph (Op Instr Bool) (Wire number) [] qs (Output number number)) :=
  letI : DecidableEq (opcodeCode (τ := Ty) (Φ := Instr) (ε := Bool)).Key :=
    inferInstanceAs (DecidableEq (Instr ⊕ Instr))
  NestedTheta.Isomorphism.check (opcodeCode (τ := Ty) (Φ := Instr) (ε := Bool)) (swapRows a b) left right

private abbrev exit : LabelDen [Silmaril.product number number] := .inl ((10 : Nat), (16 : Nat))

example : run actions s.late.toGraph 0 (point (A := number) (3 : Nat) 1) =
    some (encodeExit (exit, (133 : Nat))) := rfl

example (coherent : RegionCoherent (τ := Ty) (Φ := Instr) (ε := Bool) (m := Runtime)) :
    (Region.denote (ε := Bool) (m := Runtime) s.typing (PUnit.unit,(3 : Nat))).run 1 =
      Part.some (exit, 133) :=
  (s.finite_returns_iff actions s.relocate coherent (PUnit.unit,(3 : Nat)) exit 1 133).mp ⟨0,rfl⟩

example (fuel : Nat) : run actions s.early.toGraph fuel (point (A := number) (99 : Nat) 1) = none :=
  (s.run_eq actions fuel (99 : Nat) 1).trans rfl

#eval show IO Unit from do
  unless (checkedMap 0 1 s.early.toGraph s.late.toGraph).isSome do
    throw (IO.userError "the checker rejected an independent total pure row swap")
  -- The two ordered rows have the same typed opcode. Their token sources differ.
  unless (checkedMap 1 2 s.early.toGraph s.early.toGraph).isNone do
    throw (IO.userError "the checker accepted a reversed token dependency")

end Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Regression
