module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory
open Uflia.SExpr Uflia.Quantified Uflia.Quantified.SExpr
variable {E F : Environment}

@[simp] theorem mapPacked_sort (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} (t : PackedTerm E Γ) :
    (mapPacked f t).sort = f.sorts t.sort := rfl

/-- Successful checks transport even when the sort map identifies sorts. -/
theorem expect_mapPacked_of_eq (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} (t : PackedTerm E Γ)
    {s : SortCode String} (v : Uflia.Quantified.Term E.signature Γ s)
    (h : t.expect? s = some v) :
    (mapPacked f t).expect? (f.sorts s) = some (Hom.quantifiedTerm f v) := by
  rcases t with ⟨sort, term⟩
  unfold Uflia.Quantified.SExpr.PackedTerm.expect? at h
  split at h
  next hs =>
    change sort = s at hs
    subst sort
    change some term = some v at h
    cases Option.some.inj h
    unfold mapPacked Uflia.Quantified.SExpr.PackedTerm.expect?
    exact dite_eq_left rfl
  next hs => simp at h

theorem quantifiedTerm_heq (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ Δ : Fin k → SortCode String} {s t : SortCode String}
    (hΓ : Γ = Δ) (hs : s = t)
    (p : Uflia.Quantified.Term E.signature Γ s)
    (q : Uflia.Quantified.Term E.signature Δ t) (hp : HEq p q) :
    HEq (Hom.quantifiedTerm f p) (Hom.quantifiedTerm f q) := by
  cases hΓ
  cases hs
  cases eq_of_heq hp
  rfl

theorem quantifiedBody_heq (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} (s : SortCode String)
    (p : Uflia.Quantified.Term F.signature (f.sorts ∘ Fin.cases s Γ) (f.sorts .bool)) :
    HEq (Hom.quantifiedBody f s p) p := cast_heq _ _

@[simp] theorem quantifiedTerm_var (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} (i : Fin k) :
    Hom.quantifiedTerm f (.var i : Uflia.Quantified.Term E.signature Γ (Γ i)) = .var i := rfl

@[simp] theorem quantifiedTerm_app (f : environmentSignature E ⟶ environmentSignature F)
    {k n : Nat} {Γ : Fin k → SortCode String} {inputs : Fin n → SortCode String}
    {output : SortCode String} (op : Operation E.signature n inputs output)
    (args : ∀ i, Uflia.Quantified.Term E.signature Γ (inputs i)) :
    Hom.quantifiedTerm f (.app op args) =
      .app (Hom.operation f op) (fun i => Hom.quantifiedTerm f (args i)) := rfl

theorem quantifiedTerm_all_heq (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} (s : SortCode String)
    (body : Uflia.Quantified.Term E.signature (Fin.cases s Γ) .bool) :
    HEq (Hom.quantifiedTerm f (.all s body))
      (.all (f.sorts s) (Hom.quantifiedBody f s (Hom.quantifiedTerm f body)) :
        Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) .bool) :=
  cast_heq _ _

theorem quantifiedTerm_ex_heq (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String} (s : SortCode String)
    (body : Uflia.Quantified.Term E.signature (Fin.cases s Γ) .bool) :
    HEq (Hom.quantifiedTerm f (.ex s body))
      (.ex (f.sorts s) (Hom.quantifiedBody f s (Hom.quantifiedTerm f body)) :
        Uflia.Quantified.Term F.signature (f.sorts ∘ Γ) .bool) :=
  cast_heq _ _

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
