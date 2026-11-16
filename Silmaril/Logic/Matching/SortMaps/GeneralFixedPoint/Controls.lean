module

public import Silmaril.Logic.Matching.SortMaps.GeneralFixedPoint.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.SortMaps.GeneralControls
open CategoryTheory

abbrev A : Signature := ⟨Bool, ⟨fun _ _ _ => Empty⟩⟩
abbrev B : Signature := ⟨Unit, ⟨fun _ _ _ => Empty⟩⟩

/-- Native matching permits arbitrary sort identification. The builtin layer
separately rules out identification of its designated Int/Bool sorts. -/
def aliasMap : A ⟶ B := ⟨fun _ => (), fun op => op.elim⟩

abbrev noObjects : Fin 0 → Bool := Fin.elim0
abbrev noSets : Fin 0 → Bool := Fin.elim0
abbrev oneSet : Fin 1 → Bool := fun _ => false

/-- The same free set variable occurs in both polarities; this is admitted. -/
def mixed : GeneralFixedPoint.Pattern A.symbols oneSet noObjects false :=
  .conj (.setvar 0) (.neg (.setvar 0))

example : mixed.admissible = true := rfl
example : mixed.occurs false 0 = true := rfl
example : mixed.occurs true 0 = true := rfl
example : (Hom.generalPattern aliasMap mixed).admissible = true := by
  rw [Hom.admissible_generalPattern]
  rfl
example : (Hom.generalPattern aliasMap mixed).occurs true 0 = true := by
  rw [Hom.occurs_generalPattern]
  rfl

/-- Double negation of the local recursion variable is admitted for both μ/ν. -/
def goodMu : GeneralFixedPoint.Pattern A.symbols noSets noObjects false :=
  .mu (P' := Fin.cases false noSets) (.neg (.neg (.setvar 0)))
def goodNu : GeneralFixedPoint.Pattern A.symbols noSets noObjects false :=
  .nu (P' := Fin.cases false noSets) (.neg (.neg (.setvar 0)))
def badMu : GeneralFixedPoint.Pattern A.symbols noSets noObjects false :=
  .mu (P' := Fin.cases false noSets) (.neg (.setvar 0))

example : goodMu.admissible = true := rfl
example : goodNu.admissible = true := rfl
example : badMu.admissible = false := rfl
example : (Hom.generalPattern aliasMap badMu).admissible = false := by
  rw [Hom.admissible_generalPattern]
  rfl

theorem mixed_denotation (M : FirstOrder.Model B.symbols) (v η) :
    (Hom.generalPattern aliasMap mixed).denote M v η =
      mixed.denote (Hom.reduct aliasMap M) v η :=
  Hom.denote_generalPattern aliasMap M mixed v η

theorem mu_denotation (M : FirstOrder.Model B.symbols) (v η) :
    (Hom.generalPattern aliasMap goodMu).denote M v η =
      goodMu.denote (Hom.reduct aliasMap M) v η :=
  Hom.denote_generalPattern aliasMap M goodMu v η

theorem nu_denotation (M : FirstOrder.Model B.symbols) (v η) :
    (Hom.generalPattern aliasMap goodNu).denote M v η =
      goodNu.denote (Hom.reduct aliasMap M) v η :=
  Hom.denote_generalPattern aliasMap M goodNu v η

end Silmaril.Logic.Matching.SortMaps.GeneralControls
