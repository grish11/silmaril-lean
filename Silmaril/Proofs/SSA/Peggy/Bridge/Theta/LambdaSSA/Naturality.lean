module

public import Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA.Defs

public section

namespace Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA.Proofs

open CategoryTheory
open PEG.Bridge.Theta.Region.LambdaSSA (Primitive instruction Atom pack)
open Isotope (Value)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Region (Eval)
open RVSDG (Tuple)

universe u

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {S T U : Signature Data} {carried : List (PEG.Ty Data)}

private theorem code_id (r : Native.Code S carried) : r.map (𝟙 S) = r := by
  apply Subtype.ext
  have same : Native.opcode (𝟙 S) = id := by
    funext op
    cases op <;> rfl
  exact (congrArg (fun f => r.val.mapInstr f) same).trans (Region.mapInstr_id _)

private theorem code_comp (f : S ⟶ T) (g : T ⟶ U) (r : Native.Code S carried) :
    r.map (f ≫ g) = (r.map f).map g := by
  apply Subtype.ext
  have same : Native.opcode (f ≫ g) = Native.opcode g ∘ Native.opcode f := by
    funext op
    cases op <;> rfl
  exact (congrArg (fun f => r.val.mapInstr f) same).trans (Region.mapInstr_comp _ _ _).symm

theorem native_id (e : Native.Equation S) : e.map (𝟙 S) = e := by
  cases e
  simp only [Native.Equation.map, code_id]

theorem native_comp (f : S ⟶ T) (g : T ⟶ U) (e : Native.Equation S) :
    e.map (f ≫ g) = (e.map f).map g := by
  cases e
  simp only [Native.Equation.map, code_comp]

private theorem side_id (r : Side S carried) : r.map (𝟙 S) = r := by
  cases r
  simp only [Side.map, Theta.Side.map_id, code_id]

private theorem side_comp (f : S ⟶ T) (g : T ⟶ U) (r : Side S carried) :
    r.map (f ≫ g) = (r.map f).map g := by
  cases r
  simp only [Side.map, Theta.Side.map_comp, code_comp]

theorem checked_id (e : CheckedEquation S) : e.map (𝟙 S) = e := by
  cases e
  simp only [CheckedEquation.map, side_id]

theorem checked_comp (f : S ⟶ T) (g : T ⟶ U) (e : CheckedEquation S) :
    e.map (f ≫ g) = (e.map f).map g := by
  cases e
  simp only [CheckedEquation.map, side_comp]

theorem image_id (e : ThetaImage S) : e.map (𝟙 S) = e := by
  apply Subtype.ext
  exact Prod.ext ((thetaPlain Data).map_id S e.val.1) (native_id e.val.2)

theorem image_comp (f : S ⟶ T) (g : T ⟶ U) (e : ThetaImage S) :
    e.map (f ≫ g) = (e.map f).map g := by
  apply Subtype.ext
  exact Prod.ext ((thetaPlain Data).map_comp f g e.val.1) (native_comp f g e.val.2)

private theorem pack_reduct (f : S ⟶ T) (m : Model T)
    (values : Tuple m.val.toPEG.Value carried) :
    pack (reduct f m).val values = pack m.val values := by
  induction values with
  | nil => rfl
  | @cons t ts x xs ih =>
    exact congrArg (fun tail => Value.pair (.atom ⟨.value t, x⟩) tail) ih

private theorem eval_reduct (f : S ⟶ T) (m : Model T) (op : Primitive S.dialect.ops)
    (args : Tuple (reduct f m).val.toPEG.Value op.inputs) :
    (Native.opcode f op).eval m.val (by cases op <;> exact args) = op.eval (reduct f m).val args := by
  cases op with
  | call op => rfl
  | test => cases args with | cons flag rest => cases rest; rfl

theorem instruction_reduct (f : S ⟶ T) (m : Model T) {σ : Type u}
    (op : Primitive S.dialect.ops) (input output : Value (Atom m.val)) (start finish : σ) :
    instruction m.val (Native.opcode f op) input start output finish ↔
      instruction (reduct f m).val op input start output finish := by
  cases op <;> simp only [instruction, pack_reduct, ← eval_reduct f m]
  all_goals rfl

theorem returns_map (f : S ⟶ T) (r : Native.Code S carried) (m : Model T)
    (input output : Tuple m.val.toPEG.Value carried) :
    (r.map f).Returns m input output ↔ r.Returns (reduct f m) input output := by
  unfold Native.Code.Returns Native.Code.map
  rw [pack_reduct, pack_reduct]
  exact Eval.mapInstr_iff (Native.opcode f) (fun op input start output finish =>
    instruction_reduct f m op input output start finish) (r := r.val)

theorem native_holds_map (f : S ⟶ T) (e : Native.Equation S) (m : Model T) :
    (e.map f).Holds m ↔ e.Holds (reduct f m) := by
  constructor <;> intro holds input output
  · exact (returns_map f e.lhs m input output).symm.trans
      ((holds input output).trans (returns_map f e.rhs m input output))
  · exact (returns_map f e.lhs m input output).trans
      ((holds input output).trans (returns_map f e.rhs m input output).symm)

end Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA.Proofs
