module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBindNormalization


/-! # Native normalization of cases after binding the discriminator -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind

open Silmaril
open CfgEta.TypeCategory (returnRegion)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

/-- Reconstructing a bit with literal unit payloads agrees with returning the
same computation at the chosen exit. The computation can have effects. -/
theorem case_return_bit
    (bind : ∀ {Γ L r s}, Step Γ r s L → S Γ r s L)
    (unary : ∀ {Γ L r s}, Paper.UnaryReturn.Step Γ r s L → S Γ r s L)
    (unitEta : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → S Γ r s L)
    {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {slot : Nat}
    (ha : Tm.HasType Γ a (coprod unit unit)) (out : At L slot (coprod unit unit)) :
    Extension.Eqv S Γ
      (.case a (.let₁ .unit (.br slot (.inl (.var 0)))) (.let₁ .unit (.br slot (.inr (.var 0)))))
      ((returnRegion a).renameLabels (fun _ => slot)) L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBindNormalization.case_return_bit bind unary unitEta ha out

/-- Eliminate a case whose arms ignore their payloads when a native return-
discard proof justifies dropping its evaluated discriminator. -/
theorem case_eq_of_returnDiscards
    (bind : ∀ {Γ L r s}, Step Γ r s L → S Γ r s L)
    (unary : ∀ {Γ L r s}, Paper.UnaryReturn.Step Γ r s L → S Γ r s L)
    {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {p : Region Φ}
    (ha : Tm.HasType Γ a (coprod A B)) (hp : ValueBranches Γ p L) (drop : Extension.ReturnDiscards S Γ a) :
    Extension.Eqv S Γ (.case a (p.renameVars Nat.succ) (p.renameVars Nat.succ)) p L :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithCaseBindNormalization.case_eq_of_returnDiscards bind unary ha hp drop

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind
