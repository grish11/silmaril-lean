module

public import Silmaril.Proofs.Logic.FirstOrderLFP.FixedPoint

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP
open CategoryTheory Silmaril.Logic.Institution.Examples

theorem Formula.map_id {S : Signature} {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} (p : Formula S P Γ) : p.map (𝟙 S) = p := by
  induction p with
  | base p => exact congrArg Formula.base (FOL.Formula.map_id p)
  | pred i args => exact congrArg (Formula.pred i) (funext fun j => EQ.Term.map_id (args j))
  | conj p q hp hq => exact congrArg₂ Formula.conj hp hq
  | disj p q hp hq => exact congrArg₂ Formula.disj hp hq
  | all p hp => exact congrArg Formula.all hp
  | ex p hp => exact congrArg Formula.ex hp
  | lfp ht hpar p args hp =>
      exact congrArg₂ (Formula.lfp ht hpar) hp (funext fun j => EQ.Term.map_id (args j))

theorem Formula.map_comp {S T U : Signature} (f : S ⟶ T) (g : T ⟶ U)
    {r k : Nat} {P : Fin r → Profile S} {Γ : Fin k → S.S} (p : Formula S P Γ) :
    p.map (f ≫ g) = (p.map f).map g := by
  induction p with
  | base p => exact congrArg Formula.base (FOL.Formula.map_comp f g p)
  | pred i args => exact congrArg (Formula.pred i) (funext fun j => EQ.Term.map_comp f.toHom g.toHom (args j))
  | conj p q hp hq => exact congrArg₂ Formula.conj hp hq
  | disj p q hp hq => exact congrArg₂ Formula.disj hp hq
  | all p hp => exact congrArg Formula.all hp
  | ex p hp => exact congrArg Formula.ex hp
  | lfp ht hpar p args hp =>
      exact congrArg₂ (Formula.lfp _ _) hp (funext fun j => EQ.Term.map_comp f.toHom g.toHom (args j))

/-- Sorted signature renaming commutes with every object/predicate binder,
including the captured parameter valuation of each fixed point. -/
theorem Formula.denote_map {S T : Signature} (f : S ⟶ T) (M : Model T)
    {r k : Nat} {P : Fin r → Profile S} {Γ : Fin k → S.S} (p : Formula S P Γ) :
    (p.map f).denote M = p.denote ((reduct f).obj M) := by
  induction p with
  | base p =>
      apply OrderHom.ext
      funext η
      exact Set.ext fun ρ => FOL.Formula.holds_map f M.toStructure p ρ
  | pred i args =>
      show (Formula.pred i args |>.map f).denote M =
        (Formula.pred i args).denote ((reduct f).obj M)
      apply OrderHom.ext
      funext η
      apply Set.ext
      intro ρ
      change (fun j => ((args j).map f.toHom).eval M.toStructure.toAlgebra ρ) ∈ η i ↔
        (fun j => (args j).eval ((reduct f).obj M).toStructure.toAlgebra ρ) ∈ η i
      have he : (fun j => ((args j).map f.toHom).eval M.toStructure.toAlgebra ρ) =
          (fun j => (args j).eval ((reduct f).obj M).toStructure.toAlgebra ρ) :=
        funext fun j => EQ.Term.eval_map f.toHom M.toStructure.toAlgebra ρ (args j)
      rw [he]
      rfl
  | conj p q hp hq =>
      apply OrderHom.ext
      funext η
      change (p.map f).denote M η ∩ (q.map f).denote M η =
        p.denote ((reduct f).obj M) η ∩ q.denote ((reduct f).obj M) η
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      apply OrderHom.ext
      funext η
      change (p.map f).denote M η ∪ (q.map f).denote M η =
        p.denote ((reduct f).obj M) η ∪ q.denote ((reduct f).obj M) η
      rw [hp, hq]
      rfl
  | @all r k P Δ p hp =>
      apply OrderHom.ext
      funext η
      change {ρ | ∀ x : M.toStructure.carrier (f.sorts (Δ 0)), Fin.cases x ρ ∈ (p.map f).denote M η} =
        {ρ | ∀ x : M.toStructure.carrier (f.sorts (Δ 0)), Fin.cases x ρ ∈ p.denote ((reduct f).obj M) η}
      rw [hp]
      rfl
  | @ex r k P Δ p hp =>
      apply OrderHom.ext
      funext η
      change {ρ | ∃ x : M.toStructure.carrier (f.sorts (Δ 0)), Fin.cases x ρ ∈ (p.map f).denote M η} =
        {ρ | ∃ x : M.toStructure.carrier (f.sorts (Δ 0)), Fin.cases x ρ ∈ p.denote ((reduct f).obj M) η}
      rw [hp]
      rfl
  | @lfp r k P' Γ Δ ht hpar p args hp =>
      show (Formula.lfp ht hpar p args |>.map f).denote M =
        (Formula.lfp ht hpar p args).denote ((reduct f).obj M)
      apply OrderHom.ext
      funext η
      apply Set.ext
      intro ρ
      simp only [Formula.map]
      have he : (fun j => ((args j).map f.toHom).eval M.toStructure.toAlgebra ρ) =
          (fun j => (args j).eval ((reduct f).obj M).toStructure.toAlgebra ρ) :=
        funext fun j => EQ.Term.eval_map f.toHom M.toStructure.toAlgebra ρ (args j)
      have hF : bodyOperator M (p.map f) η ρ = bodyOperator ((reduct f).obj M) p η ρ := by
        apply OrderHom.ext
        funext X
        change {x | ∀ θ, Extends θ x ρ → θ ∈ (p.map f).denote M (insertRel M _ η X)} =
          {x | ∀ θ, Extends θ x ρ → θ ∈ p.denote ((reduct f).obj M) (insertRel ((reduct f).obj M) _ η X)}
        rw [hp]
        rfl
      change _ ∈ (bodyOperator M (p.map f) η ρ).lfp ↔
        _ ∈ (bodyOperator ((reduct f).obj M) p η ρ).lfp
      exact iff_of_eq (congrArg₂ (fun x F => x ∈ OrderHom.lfp F) he hF)

end Silmaril.Logic.FirstOrderLFP
