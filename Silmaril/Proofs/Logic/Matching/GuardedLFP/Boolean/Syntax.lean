module

public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Boolean.Isomorphism

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP.Boolean
open CategoryTheory Silmaril.Logic.Institution.Examples
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem dual_context_cast {S : Type} {A : Algebraic.ManySorted.Signature S} {r k : Nat}
    {P : Fin r → S} {Γ Δ : Fin k → S} {s : S} (h : Γ = Δ)
    (p : FixedPoint.Pattern A P Γ s) :
    (h ▸ p).dual = h ▸ p.dual := by cases h; rfl

theorem fixedPattern_dual {A B : SortMaps.Signature} (f : A ⟶ B) {r k : Nat}
    {P : Fin r → A.sorts} {Γ : Fin k → A.sorts} {s : A.sorts}
    (p : FixedPoint.Pattern A.symbols P Γ s) :
    f.fixedPattern p.dual = (f.fixedPattern p).dual := by
  induction p with
  | base p => rfl
  | setvar i => rfl
  | app op args ih =>
      change FixedPoint.Pattern.dualApp (f.operations op) (fun i => f.fixedPattern (args i).dual) =
        FixedPoint.Pattern.dualApp (f.operations op) (fun i => (f.fixedPattern (args i)).dual)
      congr 1
      funext i
      exact ih i
  | dualApp op args ih =>
      change FixedPoint.Pattern.app (f.operations op) (fun i => f.fixedPattern (args i).dual) =
        FixedPoint.Pattern.app (f.operations op) (fun i => (f.fixedPattern (args i)).dual)
      congr 1
      funext i
      exact ih i
  | conj p q hp hq => exact congrArg₂ FixedPoint.Pattern.disj hp hq
  | disj p q hp hq => exact congrArg₂ FixedPoint.Pattern.conj hp hq
  | @ex r k P Γ s bound p ih =>
      change FixedPoint.Pattern.all (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Γ) ▸ f.fixedPattern p.dual) =
          FixedPoint.Pattern.all (f.sorts bound) (((SortMaps.Hom.map_cons f bound Γ) ▸ f.fixedPattern p).dual)
      rw [ih, dual_context_cast]
  | @all r k P Γ s bound p ih =>
      change FixedPoint.Pattern.ex (f.sorts bound)
        ((SortMaps.Hom.map_cons f bound Γ) ▸ f.fixedPattern p.dual) =
          FixedPoint.Pattern.ex (f.sorts bound) (((SortMaps.Hom.map_cons f bound Γ) ▸ f.fixedPattern p).dual)
      rw [ih, dual_context_cast]
  | mu p ih => exact congrArg FixedPoint.Pattern.nu ih
  | nu p ih => exact congrArg FixedPoint.Pattern.mu ih

theorem formula_map {S T : FOL.Signature} (f : S ⟶ T) {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} {σ : Fin r → Bool} (p : FirstOrderLFP.Boolean.Formula S P Γ σ) :
    (signatureMap f).fixedPattern (formula p) = formula (p.map f) := by
  induction p with
  | base p =>
      change FixedPoint.Pattern.base ((signatureMap f).pattern ((baseSignature S).pattern (GuardedFOL.formula p))) = _
      rw [basePattern_map, GuardedFOL.formula_map]
      rfl
  | pred i positive args =>
      change tupleDefined (.conj ((signatureMap f).fixedPattern (packTerms args)) (.setvar i)) = _
      rw [packTerms_map]
      rfl
  | neg p ih =>
      change (signatureMap f).fixedPattern (formula p).dual = (formula (p.map f)).dual
      rw [fixedPattern_dual, ih]
  | conj p q hp hq => exact congrArg₂ FixedPoint.Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ FixedPoint.Pattern.disj hp hq
  | @all r k P σ Δ p ih =>
      show (signatureMap f).fixedPattern (formula (FirstOrderLFP.Boolean.Formula.all p)) =
        formula ((FirstOrderLFP.Boolean.Formula.all p).map f)
      rw [formula, all_map]
      change FixedPoint.Pattern.all (objSort (f.sorts (Δ 0))) ((context_extend (f.sorts ∘ Δ)) ▸
        (show FixedPoint.Pattern (signature T).symbols (setContext (fun i => (P i).map f))
          (objContext (f.sorts ∘ Δ)) (.base .truth) from .disj
          (.base ((signatureMap f).pattern ((baseSignature S).pattern (.neg (GuardedFOL.activeGuard Δ)))))
          ((signatureMap f).fixedPattern (formula p)))) = _
      rw [inactivePattern_map, ih]
      rfl
  | @ex r k P σ Δ p ih =>
      show (signatureMap f).fixedPattern (formula (FirstOrderLFP.Boolean.Formula.ex p)) =
        formula ((FirstOrderLFP.Boolean.Formula.ex p).map f)
      rw [formula, ex_map]
      change FixedPoint.Pattern.ex (objSort (f.sorts (Δ 0))) ((context_extend (f.sorts ∘ Δ)) ▸
        (show FixedPoint.Pattern (signature T).symbols (setContext (fun i => (P i).map f))
          (objContext (f.sorts ∘ Δ)) (.base .truth) from .conj
          (.base ((signatureMap f).pattern ((baseSignature S).pattern (GuardedFOL.activeGuard Δ))))
          ((signatureMap f).fixedPattern (formula p)))) = _
      rw [activePattern_map, ih]
      rfl
  | lfp ht hp body args ih =>
      change tupleDefined (.conj ((signatureMap f).fixedPattern (packTerms args))
        (.mu ((signatureMap f).fixedPattern (tupleBody ht hp (formula body))))) = _
      rw [packTerms_map, tupleBody_map, ih]
      rfl


/-- The stronger compiler agrees syntactically with the original positive map;
conservative inclusion does not alter any positive pattern or binder. -/
theorem formula_positiveWith {S : FOL.Signature} {r k : Nat}
    {P : Fin r → Profile S} {Γ : Fin k → S.S} (p : FirstOrderLFP.Formula S P Γ)
    (σ : Fin r → Bool) (hσ : ∀ i, σ i = true) :
    formula (FirstOrderLFP.Boolean.positiveWith p σ hσ) = GuardedLFP.formula p := by
  induction p with
  | base p => rfl
  | pred i args => rfl
  | conj p q hp hq => exact congrArg₂ FixedPoint.Pattern.conj (hp σ hσ) (hq σ hσ)
  | disj p q hp hq => exact congrArg₂ FixedPoint.Pattern.disj (hp σ hσ) (hq σ hσ)
  | @all r k P Δ p ih =>
      change FixedPoint.Pattern.all (objSort (Δ 0)) ((context_extend Δ) ▸
        (show FixedPoint.Pattern (signature S).symbols (setContext P) (objContext Δ) (.base .truth) from .disj (.base ((baseSignature S).pattern (.neg (GuardedFOL.activeGuard Δ))))
          (formula (FirstOrderLFP.Boolean.positiveWith p σ hσ)))) = _
      rw [ih]
      rfl
  | @ex r k P Δ p ih =>
      change FixedPoint.Pattern.ex (objSort (Δ 0)) ((context_extend Δ) ▸
        (show FixedPoint.Pattern (signature S).symbols (setContext P) (objContext Δ) (.base .truth) from .conj (.base ((baseSignature S).pattern (GuardedFOL.activeGuard Δ)))
          (formula (FirstOrderLFP.Boolean.positiveWith p σ hσ)))) = _
      rw [ih]
      rfl
  | lfp ht hp body args ih =>
      change tupleDefined (.conj (packTerms args)
        (.mu (tupleBody ht hp (formula (FirstOrderLFP.Boolean.positiveWith body
          (Fin.cases true σ) (fun i => Fin.cases rfl hσ i)))))) = _
      rw [ih]
      rfl

end Silmaril.Logic.Matching.GuardedLFP.Boolean
