module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms

@[expose] public section

open Silmaril.Isotope Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs

variable {Φ ε : Type} [HasTy Φ (Ty Unit)] [HasEff Φ ε] {pe : ε}

local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "H" => HasType Φ Free
local notation "E" => AbortEquiv (Φ := Φ) pe Free

def nativeValue (Φ : Type) {n : Nat} : (c : Code) → c.Value → Tm Empty Φ n
  | .unit, _ => .unit
  | .sum l _, .inl v => .inl (nativeValue Φ l v)
  | .sum _ r, .inr v => .inr (nativeValue Φ r v)

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] in
theorem value_lowers (c : Code) (v : c.Value) (n : Nat) :
    (c.literal v).toLetIter n = some (nativeValue Φ c v) := by
  induction c with
  | unit => rfl
  | sum l r il ir => cases v <;> simp [Code.literal, Expr.toLetIter, nativeValue, il, ir]

omit [HasEff Φ ε] in
theorem value_typed (c : Code) (v : c.Value) {n : Nat} (β : BoundCtx (Ty Unit) n) :
    H β (nativeValue Φ c v) c.ty := by
  induction c with
  | unit => exact .unit
  | sum l r il ir => cases v with
    | inl x => exact .inl (il x)
    | inr x => exact .inr (ir x)

omit [HasTy Φ (Ty Unit)] in
theorem value_pure (c : Code) (v : c.Value) (n : Nat) : Pure pe (nativeValue Φ c v (n := n)) := by
  induction c with
  | unit => exact .unit
  | sum l r il ir => cases v with
    | inl x => exact .inl (il x)
    | inr x => exact .inr (ir x)

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] in
@[simp] theorem value_bsubst {n m : Nat} (σ : Fin n → Tm Empty Φ m) (c : Code) (v : c.Value) :
    (nativeValue Φ c v).bsubst σ = nativeValue Φ c v := by
  induction c with
  | unit => rfl
  | sum l r il ir => cases v <;> simp [nativeValue, Tm.bsubst, il, ir]

/-- Specialize the single input of a term into any target context. -/
def plug {n : Nat} (t : Tm Empty Φ 1) (v : Tm Empty Φ n) : Tm Empty Φ n :=
  t.bsubst (fun _ => v)

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] in
theorem plug_eq_instantiate (t : Tm Empty Φ 1) (v : Tm Empty Φ 0) :
    plug t v = t.instantiate v := by
  apply Tm.bsubst_congr
  intro i
  rw [Fin.eq_zero i]
  rfl

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] in
theorem instantiate_under (t : Tm Empty Φ 1) (v : Tm Empty Φ 1) :
    t.underBinder.instantiate v = plug t v := by
  unfold Tm.instantiate Tm.underBinder plug
  rw [Tm.bsubst_rename]
  apply Tm.bsubst_congr
  intro i
  rw [Fin.eq_zero i]
  rfl

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] in
private theorem instantiate_under_twice (t : Tm Empty Φ 1) (v : Tm Empty Φ 1) :
    t.underBinder.underBinder.instantiate v.underBinder = (plug t v).underBinder := by
  unfold Tm.instantiate Tm.underBinder plug
  rw [Tm.bsubst_rename, Tm.bsubst_rename, Tm.rename_bsubst]
  apply Tm.bsubst_congr
  intro i
  rw [Fin.eq_zero i]
  rfl

omit [HasTy Φ (Ty Unit)] [HasEff Φ ε] in
private theorem plug_bv (t : Tm Empty Φ 1) : plug t (.bv 0) = t := by
  have eq : (fun _ : Fin 1 => (.bv 0 : Tm Empty Φ 1)) = Tm.bv := by
    funext i
    rw [Fin.eq_zero i]
  rw [plug, eq, Tm.bsubst_bv_eq_rename, Tm.rename_id]

theorem plug_typed {t : Tm Empty Φ 1} {m : Nat} {β : BoundCtx (Ty Unit) m}
    {v : Tm Empty Φ m} {A C : Ty Unit} (ht : H (.snoc .nil A) t C) (hv : H β v A) :
    H β (plug t v) C := by
  apply ht.bsubst
  intro i
  rw [Fin.eq_zero i]
  exact hv

private theorem rename_repaired {n m : Nat} {β : BoundCtx (Ty Unit) n} {δ : BoundCtx (Ty Unit) m}
    {a b : Tm Empty Φ n} {C : Ty Unit} (h : E β a b C) (r : TypedRenaming β δ) :
    E δ (a.rename r.toFun) (b.rename r.toFun) C := by
  refine Refinement.rename (fun ren law => ?_) h r
  cases law with
  | sequence ht => exact .sequence (ht.rename ren)
  | unsequence ht => exact .unsequence (ht.rename ren)

private theorem rebuild_unit {a : Tm Empty Φ 1} {C : Ty Unit} (ha : H (.snoc .nil .unit) a C) :
    E (.snoc .nil .unit) a (plug a (.unit : Tm Empty Φ 0)).lift C := by
  have v : H (.snoc .nil .unit) (.bv 0 : Tm Empty Φ 1) .unit := .bv
  have rebind := Equiv.letBeta (pureEff := pe) .bv v ha.underBinder
  rw [instantiate_under, plug_bv] at rebind
  have unitEq : Equiv pe Free (.snoc .nil .unit) (.bv 0 : Tm Empty Φ 1) .unit .unit :=
    (Equiv.unitEta v).symm.trans (Equiv.letBeta .bv v .unit)
  have beta := Equiv.letBeta (pureEff := pe) .unit (HasType.unit (β := .snoc .nil .unit)) ha.underBinder
  rw [instantiate_under] at beta
  have move : plug a (.unit : Tm Empty Φ 1) = (plug a (.unit : Tm Empty Φ 0)).lift := by
    simp only [plug, Tm.lift, Tm.rename_bsubst, Tm.rename]
  rw [move] at beta
  exact .equiv (rebind.symm.trans ((Equiv.let₁ unitEq (.refl ha.underBinder)).trans beta))

private theorem rebuild_sum {a : Tm Empty Φ 1} {A B C : Ty Unit}
    (ha : H (.snoc .nil (Ty.coprod A B)) a C) :
    E (.snoc .nil (Ty.coprod A B)) a
      (.case (.bv 0) (plug a (.inl (.bv 0) : Tm Empty Φ 1)).underBinder
        (plug a (.inr (.bv 0) : Tm Empty Φ 1)).underBinder) C := by
  have v : H (.snoc .nil (Ty.coprod A B)) (.bv 0 : Tm Empty Φ 1) (Ty.coprod A B) := .bv
  have vL : H (.snoc (.snoc .nil (Ty.coprod A B)) A) (.inl (.bv 0)) (Ty.coprod A B) := .inl .bv
  have vR : H (.snoc (.snoc .nil (Ty.coprod A B)) B) (.inr (.bv 0)) (Ty.coprod A B) := .inr .bv
  have rebind := Equiv.letBeta (pureEff := pe) .bv v ha.underBinder
  rw [instantiate_under, plug_bv] at rebind
  have left := Equiv.letBeta (pureEff := pe) (.inl .bv) vL ha.underBinder.underBinder
  have right := Equiv.letBeta (pureEff := pe) (.inr .bv) vR ha.underBinder.underBinder
  change Equiv pe Free _ _ (a.underBinder.underBinder.instantiate
    (Tm.inl (.bv 0) : Tm Empty Φ 1).underBinder) C at left
  change Equiv pe Free _ _ (a.underBinder.underBinder.instantiate
    (Tm.inr (.bv 0) : Tm Empty Φ 1).underBinder) C at right
  rw [instantiate_under_twice] at left right
  exact .equiv (rebind.symm.trans ((Equiv.let₁ (Equiv.caseEta v).symm (.refl ha.underBinder)).trans
    ((Equiv.bindLetCase v vL vR ha.underBinder).trans (.case (.refl v) left right))))

/-- A native equation over a finite constructor code follows from all
closed specializations. This includes terms containing native iteration. -/
theorem by_values (c : Code) {a b : Tm Empty Φ 1} {C : Ty Unit}
    (ha : H (.snoc .nil c.ty) a C) (hb : H (.snoc .nil c.ty) b C)
    (rows : ∀ s : c.Value, E .nil (plug a (nativeValue Φ c s)) (plug b (nativeValue Φ c s)) C) :
    E (.snoc .nil c.ty) a b C := by
  induction c generalizing a b with
  | unit =>
    exact (rebuild_unit ha).trans ((rename_repaired (rows PUnit.unit) (TypedRenaming.succ .nil .unit)).trans
      (rebuild_unit hb).symm)
  | sum l r il ir =>
    let injL : Tm Empty Φ 1 := .inl (.bv 0)
    let injR : Tm Empty Φ 1 := .inr (.bv 0)
    have hL : H (.snoc .nil l.ty) injL (Ty.coprod l.ty r.ty) := .inl .bv
    have hR : H (.snoc .nil r.ty) injR (Ty.coprod l.ty r.ty) := .inr .bv
    have left := il (plug_typed ha hL) (plug_typed hb hL) (fun s => by
        simp only [plug, Tm.bsubst_comp, injL, Tm.bsubst]
        exact rows (.inl s))
    have right := ir (plug_typed ha hR) (plug_typed hb hR) (fun s => by
        simp only [plug, Tm.bsubst_comp, injR, Tm.bsubst]
        exact rows (.inr s))
    exact (rebuild_sum ha).trans ((Refinement.case (.equiv (.refl .bv))
      (rename_repaired left (TypedRenaming.underBinder .nil (Ty.coprod l.ty r.ty) l.ty))
      (rename_repaired right (TypedRenaming.underBinder .nil (Ty.coprod l.ty r.ty) r.ty))).trans
      (rebuild_sum hb).symm)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs
