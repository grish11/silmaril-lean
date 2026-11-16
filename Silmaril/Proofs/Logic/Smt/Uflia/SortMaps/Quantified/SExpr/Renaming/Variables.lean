module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Core.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory Uflia.SExpr Uflia.Quantified
variable {E F : Environment}

/-- Variable references retain their actual de Bruijn index while sorts change. -/
def mapRef (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} {s : SortCode String} :
    Ref Γ s → Ref (f.sorts ∘ Γ) (f.sorts s)
  | .index i => .index i

private theorem ref_index_heq {k : Nat} {Γ Δ : Fin k → SortCode String}
    (h : Γ = Δ) (i : Fin k) :
    HEq (Ref.index i : Ref Γ (Γ i)) (Ref.index i : Ref Δ (Δ i)) := by
  cases h
  rfl

theorem mapRef_succ_heq (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} {s : SortCode String}
    (r : Ref Γ s) (sort : SortCode String) :
    HEq (mapRef f (r.succ sort)) ((mapRef f r).succ (f.sorts sort)) := by
  cases r with
  | index i => exact ref_index_heq (Hom.sorts_cons f sort Γ) i.succ

theorem mapRef_term (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} {s : SortCode String}
    (r : Ref Γ s) :
    Hom.quantifiedTerm f (r.term : Uflia.Quantified.Term E.signature Γ s) =
      (mapRef f r).term := by
  cases r
  rfl

theorem mapRef_lift_heq (f : environmentSignature E ⟶ environmentSignature F)
    {k l : Nat} {Γ : Fin k → SortCode String} {Δ : Fin l → SortCode String}
    (r : ∀ i, Ref Δ (Γ i)) (sort : SortCode String) (i : Fin (k + 1)) :
    HEq (mapRef f (Ref.lift r sort i))
      (Ref.lift (fun j => mapRef f (r j)) (f.sorts sort) i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ref_index_heq (Hom.sorts_cons f sort Δ) 0
  · exact mapRef_succ_heq f (r j) sort

/-- Renaming respects equality casts in both its source and target contexts. -/
theorem term_rename_heq {k l : Nat}
    {Γ Γ' : Fin k → SortCode String} {Δ Δ' : Fin l → SortCode String}
    {s s' : SortCode String} (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hs : s = s')
    (p : Uflia.Quantified.Term F.signature Γ s)
    (q : Uflia.Quantified.Term F.signature Γ' s') (hp : HEq p q)
    (r : ∀ i, Ref Δ (Γ i)) (r' : ∀ i, Ref Δ' (Γ' i))
    (hr : ∀ i, HEq (r i) (r' i)) : HEq (p.rename r) (q.rename r') := by
  cases hΓ
  cases hΔ
  cases hs
  cases eq_of_heq hp
  have same : r = r' := funext (fun i => eq_of_heq (hr i))
  cases same
  rfl

private theorem all_heq {k : Nat} {Γ : Fin k → SortCode String}
    (sort : SortCode String)
    (p q : Uflia.Quantified.Term F.signature (Fin.cases sort Γ) .bool)
    (h : HEq p q) : HEq (Uflia.Quantified.Term.all sort p)
      (Uflia.Quantified.Term.all sort q) := by
  cases eq_of_heq h
  rfl

private theorem ex_heq {k : Nat} {Γ : Fin k → SortCode String}
    (sort : SortCode String)
    (p q : Uflia.Quantified.Term F.signature (Fin.cases sort Γ) .bool)
    (h : HEq p q) : HEq (Uflia.Quantified.Term.ex sort p)
      (Uflia.Quantified.Term.ex sort q) := by
  cases eq_of_heq h
  rfl

/-- Full quantified syntax transport commutes with capture-safe local renaming. -/
theorem quantifiedTerm_rename (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} {s : SortCode String}
    (term : Uflia.Quantified.Term E.signature Γ s) :
    ∀ {l : Nat} {Δ : Fin l → SortCode String} (r : ∀ i, Ref Δ (Γ i)),
      Hom.quantifiedTerm f (term.rename r) =
        (Hom.quantifiedTerm f term).rename (fun i => mapRef f (r i)) := by
  induction term with
  | var i =>
    intro l Δ r
    exact mapRef_term f (r i)
  | app op args ih =>
    intro l Δ r
    simp only [Term.rename, Hom.quantifiedTerm]
    congr 1
    funext i
    exact ih i r
  | @all k Γ sort body ih =>
    intro l Δ r
    have bodySame : HEq
        (Hom.quantifiedBody f sort (Hom.quantifiedTerm f (body.rename (Ref.lift r sort))))
        ((Hom.quantifiedBody f sort (Hom.quantifiedTerm f body)).rename
          (Ref.lift (fun i => mapRef f (r i)) (f.sorts sort))) := by
      apply (quantifiedBody_heq f sort _).trans
      rw [ih (Ref.lift r sort)]
      exact term_rename_heq (Hom.sorts_cons f sort Γ) (Hom.sorts_cons f sort Δ)
        f.bool (Hom.quantifiedTerm f body) (Hom.quantifiedBody f sort (Hom.quantifiedTerm f body))
        (quantifiedBody_heq f sort _).symm _ _ (mapRef_lift_heq f r sort)
    have outer := quantifiedTerm_all_heq f sort (body.rename (Ref.lift r sort))
    have renamed := term_rename_heq rfl rfl f.bool
      (Hom.quantifiedTerm f (.all sort body))
      (.all (f.sorts sort) (Hom.quantifiedBody f sort (Hom.quantifiedTerm f body)))
      (quantifiedTerm_all_heq f sort body) (fun i => mapRef f (r i))
      (fun i => mapRef f (r i)) (fun _ => HEq.rfl)
    exact eq_of_heq (outer.trans ((all_heq (f.sorts sort) _ _ bodySame).trans renamed.symm))
  | @ex k Γ sort body ih =>
    intro l Δ r
    have bodySame : HEq
        (Hom.quantifiedBody f sort (Hom.quantifiedTerm f (body.rename (Ref.lift r sort))))
        ((Hom.quantifiedBody f sort (Hom.quantifiedTerm f body)).rename
          (Ref.lift (fun i => mapRef f (r i)) (f.sorts sort))) := by
      apply (quantifiedBody_heq f sort _).trans
      rw [ih (Ref.lift r sort)]
      exact term_rename_heq (Hom.sorts_cons f sort Γ) (Hom.sorts_cons f sort Δ)
        f.bool (Hom.quantifiedTerm f body) (Hom.quantifiedBody f sort (Hom.quantifiedTerm f body))
        (quantifiedBody_heq f sort _).symm _ _ (mapRef_lift_heq f r sort)
    have outer := quantifiedTerm_ex_heq f sort (body.rename (Ref.lift r sort))
    have renamed := term_rename_heq rfl rfl f.bool
      (Hom.quantifiedTerm f (.ex sort body))
      (.ex (f.sorts sort) (Hom.quantifiedBody f sort (Hom.quantifiedTerm f body)))
      (quantifiedTerm_ex_heq f sort body) (fun i => mapRef f (r i))
      (fun i => mapRef f (r i)) (fun _ => HEq.rfl)
    exact eq_of_heq (outer.trans ((ex_heq (f.sorts sort) _ _ bodySame).trans renamed.symm))

/-- The only mismatch is the explicit mapped binder-context equality. -/
theorem quantifiedTerm_weaken_heq (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} {s : SortCode String}
    (term : Uflia.Quantified.Term E.signature Γ s) (sort : SortCode String) :
    HEq (Hom.quantifiedTerm f (term.weaken sort))
      ((Hom.quantifiedTerm f term).weaken (f.sorts sort)) := by
  have mapped := quantifiedTerm_rename f term (Δ := Fin.cases sort Γ)
    (fun i => Ref.index i.succ)
  apply (heq_of_eq mapped).trans
  exact term_rename_heq rfl (Hom.sorts_cons f sort Γ) rfl _ _ HEq.rfl
    (fun i => mapRef f (Ref.index i.succ)) (fun i => Ref.index i.succ)
    (fun i => ref_index_heq (Hom.sorts_cons f sort Γ) i.succ)

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
