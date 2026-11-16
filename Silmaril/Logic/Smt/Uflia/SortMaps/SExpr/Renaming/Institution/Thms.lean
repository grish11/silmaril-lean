module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Institution

/-- One common model serves the whole source theory and its decoded image. -/
theorem satisfiable_iff_decode (S : PrefixSignature)
    (Γ : Set (Sentence S.prefix.environment)) :
    (room S).Satisfiable Γ ↔
      (SortMaps.room (environmentSignature S.prefix.environment)).Satisfiable
        (Uflia.SExpr.Renaming.Concrete.Sentence.decode '' Γ) :=
  (toAbstract.ρ.app S).satisfiable_map_iff_of_elemExpansive
    (toAbstract_modelExpansive S).elemExpansive Γ

theorem unsatisfiable_iff_decode (S : PrefixSignature)
    (Γ : Set (Sentence S.prefix.environment)) :
    (room S).Unsatisfiable Γ ↔
      (SortMaps.room (environmentSignature S.prefix.environment)).Unsatisfiable
        (Uflia.SExpr.Renaming.Concrete.Sentence.decode '' Γ) :=
  not_congr (satisfiable_iff_decode S Γ)

theorem entails_iff_decode (S : PrefixSignature)
    (Γ : Set (Sentence S.prefix.environment)) (φ : Sentence S.prefix.environment) :
    (room S).Entails Γ φ ↔
      (SortMaps.room (environmentSignature S.prefix.environment)).Entails
        (Uflia.SExpr.Renaming.Concrete.Sentence.decode '' Γ) φ.decode :=
  (toAbstract.ρ.app S).entails_map_iff (toAbstract_modelExpansive S) Γ φ

end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
