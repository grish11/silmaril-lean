module

public import Silmaril.Logic.Matching.GuardedFOL.Structure

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {S T : FOL.Signature}

theorem term_map (f : S ⟶ T) {k : Nat} {Γ : Fin k → S.S} {s : S.S}
    (t : EQ.Term S.toSignature Γ s) :
    SortMaps.Hom.pattern (signatureMap f) (term t) = term (t.map f.toHom) := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (FirstOrder.Pattern.app (Operation.function (f.ops op))) (funext ih)

private theorem pattern_cast {A B : SortMaps.Signature} (f : A ⟶ B) {k : Nat}
    {Γ Δ : Fin k → A.sorts} {s : A.sorts} (h : Γ = Δ) (p : FirstOrder.Pattern A.symbols Γ s) :
    SortMaps.Hom.pattern f (h ▸ p) = congrArg (f.sorts ∘ ·) h ▸ SortMaps.Hom.pattern f p := by cases h; rfl

private theorem transport_heq {A : SortMaps.Signature} {k : Nat} {Γ Δ : Fin k → A.sorts}
    {s : A.sorts} (h : Γ = Δ) (p : FirstOrder.Pattern A.symbols Γ s) :
    HEq (h ▸ p : FirstOrder.Pattern A.symbols Δ s) p := by cases h; rfl

private theorem cast_neg {A : SortMaps.Signature} {k : Nat} {Γ Δ : Fin k → A.sorts}
    {s : A.sorts} (h : Γ = Δ) (p : FirstOrder.Pattern A.symbols Γ s) :
    (h ▸ FirstOrder.Pattern.neg p) = FirstOrder.Pattern.neg (h ▸ p) := by cases h; rfl

theorem allContext_map (f : S ⟶ T) {k : Nat} {Γ : Fin k → S.S} {Δ : Fin (k+1) → S.S}
    (h : Δ ∘ Fin.succ = Γ) (p : FirstOrder.Pattern (signature S).symbols (objContext Δ) .truth) :
    SortMaps.Hom.pattern (signatureMap f) (allContext h p) =
      allContext (congrArg (f.sorts ∘ ·) h) (SortMaps.Hom.pattern (signatureMap f) p) := by
  simp only [allContext, SortMaps.Hom.pattern, pattern_cast (signatureMap f), cast_neg (A := signature T)]
  congr 3
  apply eq_of_heq
  exact (transport_heq (SortMaps.Hom.map_cons (signatureMap f) (.object (Δ 0)) (objContext Γ)) _).trans
    ((transport_heq (congrArg ((signatureMap f).sorts ∘ ·) (context_extend h)) _).trans
      (transport_heq (context_extend (congrArg (f.sorts ∘ ·) h)) _).symm)

private theorem active_map (f : S ⟶ T) {k : Nat} {Γ : Fin k → MatchingSort S} (s : S.S) :
    SortMaps.Hom.pattern (signatureMap f) (FirstOrder.Pattern.app (A := (signature S).symbols) (Γ := Γ) (.active s) (fun i => i.elim0)) =
      FirstOrder.Pattern.app (A := (signature T).symbols) (.active (f.sorts s)) (fun i => i.elim0) := by
  change FirstOrder.Pattern.app (A := (signature T).symbols) (Operation.active (f.sorts s)) _ = FirstOrder.Pattern.app (A := (signature T).symbols) (Operation.active (f.sorts s)) _
  congr 1
  funext i
  exact i.elim0

theorem activeGuard_map (f : S ⟶ T) {k : Nat} (Δ : Fin (k+1) → S.S) :
    SortMaps.Hom.pattern (signatureMap f) (activeGuard Δ) = activeGuard (f.sorts ∘ Δ) := by
  change defined (S := T) (.conj (.var 0)
    (SortMaps.Hom.pattern (signatureMap f)
      (.app (Γ := objContext Δ) (.active (Δ 0)) (fun i => i.elim0)))) = _
  rw [active_map]
  rfl

theorem formula_map (f : S ⟶ T) {k : Nat} {Γ : Fin k → S.S} (p : FOL.Formula S Γ) :
    SortMaps.Hom.pattern (signatureMap f) (formula p) = formula (p.map f) := by
  induction p with
  | eq t u =>
      change defined (.conj (SortMaps.Hom.pattern (signatureMap f) (term t))
        (SortMaps.Hom.pattern (signatureMap f) (term u))) = _
      rw [term_map, term_map]
      rfl
  | rel r args =>
      exact congrArg (FirstOrder.Pattern.app (Operation.relation (f.rels r))) (funext fun i => term_map f (args i))
  | tt =>
      change FirstOrder.Pattern.app (A := (signature T).symbols) (Operation.truth (S := T)) _ = FirstOrder.Pattern.app (A := (signature T).symbols) (Operation.truth (S := T)) _
      congr 1
      funext i
      exact i.elim0
  | not p ih => exact congrArg FirstOrder.Pattern.neg ih
  | and p q hp hq => exact congrArg₂ FirstOrder.Pattern.conj hp hq
  | @all k Γ Δ h p ih =>
      rw [formula, allContext_map]
      change allContext _ (imp (SortMaps.Hom.pattern (signatureMap f) (activeGuard Δ))
        (SortMaps.Hom.pattern (signatureMap f) (formula p))) = _
      rw [activeGuard_map, ih]
      rfl
end Silmaril.Logic.Matching.GuardedFOL
