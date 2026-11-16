module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Receipts.Defs

set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

theorem SourceSentence.satisfies_lower {A : Package}
    (M : @Model A.base.bindings A.base.scope A.base.literalPrefix A.base.literals A.base.hooks)
    (p : SourceSentence A) :
    p.Satisfies M ↔ Matching.GeneralFixedPoint.Sentence.Satisfies
      (@Model.native A.base.bindings _ _ _ _ M) p.lower :=
  @CheckedSentence.satisfies_lower A.base.bindings A.base.scope A.base.literals
    A.base.literalPrefix A.base.hooks M p.toChecked

private theorem sentence_recontext {scope : Kore.Modules.Scope}
    {P Q Γ Δ : ContextData} {s : String} (hP : P = Q) (hΓ : Γ = Δ)
    (p : Matching.GeneralFixedPoint.Pattern scope.signature P.2 Γ.2 s)
    (q : Matching.GeneralFixedPoint.Pattern scope.signature Q.2 Δ.2 s)
    (hp : HEq p q) (ap : p.admissible = true) (aq : q.admissible = true) :
    (⟨P.1, Γ.1, P.2, Γ.2, s, p, ap⟩ : Matching.GeneralFixedPoint.Sentence scope.signature) =
      ⟨Q.1, Δ.1, Q.2, Δ.2, s, q, aq⟩ := by
  cases hP
  cases hΓ
  cases hp
  rfl

/-- The lower/native square for every actual source receipt, including alias
substitution, literals and both recursive binders. -/
theorem SourceSentence.mapStep_lower {A B : Package} (f : Step A B)
    (profiles : literalProfiles A = true) (p : SourceSentence A) :
    (p.mapStep f profiles).lower =
      Matching.SortMaps.Hom.generalSentence f.semantic.native p.lower := by
  exact sentence_recontext (scope := B.base.scope)
    (namesData_mapNames f.semantic.native.sorts p.sets)
    (namesData_mapNames f.semantic.native.sorts p.objects)
    _ _ (reindexPattern_heq f p.typed) _ _

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
