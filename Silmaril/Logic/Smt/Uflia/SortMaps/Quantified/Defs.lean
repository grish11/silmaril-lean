module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Hom
open CategoryTheory
variable {A B C : Signature}

/-- Equality transport of the extended binder context and the fixed Boolean result. -/
def quantifiedBody (f : A ⟶ B) {k : Nat} {Γ : Fin k → SortCode A.users}
    (s : SortCode A.users)
    (p : Quantified.Term B.symbols (f.sorts ∘ Fin.cases s Γ) (f.sorts .bool)) :
    Quantified.Term B.symbols (Fin.cases (f.sorts s) (f.sorts ∘ Γ)) .bool :=
  cast (congrArg₂ (fun ctx out => Quantified.Term B.symbols ctx out)
    (sorts_cons f s Γ) f.bool) p

/-- Reindex the full quantified term syntax, including quantified Boolean terms
in arbitrary UF arguments, equality operands and conditional guards. -/
def quantifiedTerm (f : A ⟶ B) : {k : Nat} → {Γ : Fin k → SortCode A.users} →
    {s : SortCode A.users} → Quantified.Term A.symbols Γ s →
    Quantified.Term B.symbols (f.sorts ∘ Γ) (f.sorts s) := by
  intro k Γ s t
  exact match t with
  | .var i => .var i
  | .app op args => .app (operation f op) (fun i => quantifiedTerm f (args i))
  | .all s body =>
    cast (congrArg (Quantified.Term B.symbols (f.sorts ∘ Γ)) f.bool.symm)
      (.all (f.sorts s) (quantifiedBody f s (quantifiedTerm f body)))
  | .ex s body =>
    cast (congrArg (Quantified.Term B.symbols (f.sorts ∘ Γ)) f.bool.symm)
      (.ex (f.sorts s) (quantifiedBody f s (quantifiedTerm f body)))

def quantifiedSentence (f : A ⟶ B) (p : Quantified.Sentence A.symbols) :
    Quantified.Sentence B.symbols :=
  cast (congrArg₂ (fun ctx out => Quantified.Term B.symbols ctx out)
    (sorts_empty f) f.bool) (quantifiedTerm f p)

end Silmaril.Logic.Smt.Uflia.SortMaps.Hom
