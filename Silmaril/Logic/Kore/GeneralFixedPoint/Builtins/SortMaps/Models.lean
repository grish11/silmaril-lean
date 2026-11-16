module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
open CategoryTheory

/-- Nullary profiles have a unique index function; no assumption on names or
carrier emptiness is used to reuse the existing literal law. -/
theorem Laws.literal_inputs {bindings : SortBindings} {scope : Kore.Modules.Scope}
    {literalPrefix : String} {literals : List LiteralBinding} {hooks : List HookBinding}
    {M : Matching.GeneralFixedPoint.Model scope.signature}
    {B : @Carriers bindings scope M}
    (laws : @Laws bindings scope M literalPrefix literals hooks B)
    (b : LiteralBinding) (member : b ∈ literals) (l : Literal) (value : b.literal = l)
    {inputs : Fin 0 → String}
    (op : scope.signature.operations 0 inputs (@Literal.sort bindings l))
    (identity : op.val = b.symbol) :
    M.operation op (fun i => i.elim0) = {B.literal l} := by
  have empty : inputs = fun i => i.elim0 := funext (fun i => i.elim0)
  subst inputs
  exact laws.literal b member l value op identity

namespace SortMaps.Hom

/-- Actual restricted builtin model reduct. The proof normalizes the endpoint
name equalities by eliminating the target binding names; the source carrier
equivalences then have exactly the target equivalence types. All three builtin
laws are proved from retained actual target declaration bindings. -/
def reduct {A B : Signature} (f : A ⟶ B)
    (M : @Model B.bindings B.scope B.literalPrefix B.literals B.hooks) :
    @Model A.bindings A.scope A.literalPrefix A.literals A.hooks := by
  rcases A with ⟨⟨ai, ab, ad⟩, scopeA, prefixA, literalsA, hooksA⟩
  rcases B with ⟨⟨bi, bb, bd⟩, scopeB, prefixB, literalsB, hooksB⟩
  rcases f with ⟨f, hi, hb, labels⟩
  change ((⟨String, scopeA.signature⟩ : Matching.SortMaps.Signature) ⟶
    (⟨String, scopeB.signature⟩ : Matching.SortMaps.Signature)) at f
  change f.sorts ai = bi at hi
  change f.sorts ab = bb at hb
  subst bi
  subst bb
  let sourceBindings : SortBindings := ⟨ai, ab, ad⟩
  let targetBindings : SortBindings := ⟨f.sorts ai, f.sorts ab, bd⟩
  let targetNative := @Model.native targetBindings scopeB prefixB literalsB hooksB M
  let targetCarriers := @Model.carriers targetBindings scopeB prefixB literalsB hooksB M
  let targetLaws := @Model.laws targetBindings scopeB prefixB literalsB hooksB M
  let sourceNative := Matching.SortMaps.Hom.reduct f targetNative
  let sourceCarriers : @Carriers sourceBindings scopeA sourceNative :=
    @Carriers.mk sourceBindings scopeA sourceNative
      (@Carriers.integer targetBindings scopeB targetNative targetCarriers)
      (@Carriers.boolean targetBindings scopeB targetNative targetCarriers)
  refine @Model.mk sourceBindings scopeA prefixA literalsA hooksA
    sourceNative sourceCarriers ?_
  refine @Laws.mk sourceBindings scopeA sourceNative prefixA literalsA hooksA sourceCarriers ?_ ?_ ?_
  · intro b member l value op identity
    obtain ⟨c, targetMember, sameSymbol, sameLiteral⟩ :=
      labels op (show Label.literal l ∈ _ from ⟨b, member, identity.symm, value⟩)
    cases l with
    | integer n =>
      exact Laws.literal_inputs (bindings := targetBindings) targetLaws c targetMember (.integer n) sameLiteral
        (f.operations op) sameSymbol.symm
    | boolean boolValue =>
      exact Laws.literal_inputs (bindings := targetBindings) targetLaws c targetMember (.boolean boolValue) sameLiteral
        (f.operations op) sameSymbol.symm
  · intro b member hook op identity args
    obtain ⟨c, targetMember, sameSymbol, sameHook⟩ :=
      labels op (show Label.hook .intEq ∈ _ from ⟨b, member, identity.symm, hook⟩)
    exact @Laws.intEq targetBindings scopeB targetNative prefixB literalsB hooksB
      targetCarriers targetLaws c targetMember sameHook (f.operations op) sameSymbol.symm args
  · intro b member hook op identity args
    obtain ⟨c, targetMember, sameSymbol, sameHook⟩ :=
      labels op (show Label.hook .boolNot ∈ _ from ⟨b, member, identity.symm, hook⟩)
    exact @Laws.boolNot targetBindings scopeB targetNative prefixB literalsB hooksB
      targetCarriers targetLaws c targetMember sameHook (f.operations op) sameSymbol.symm args

/-- The restricted reduct really has the existing independently defined native
reduct, despite the dependent endpoint-name normalization used in its proof. -/
theorem reduct_native {A B : Signature} (f : A ⟶ B)
    (M : @Model B.bindings B.scope B.literalPrefix B.literals B.hooks) :
    @Model.native A.bindings A.scope A.literalPrefix A.literals A.hooks (reduct f M) =
      Matching.SortMaps.Hom.reduct f.native
        (@Model.native B.bindings B.scope B.literalPrefix B.literals B.hooks M) := by
  rcases A with ⟨⟨ai, ab, ad⟩, scopeA, prefixA, literalsA, hooksA⟩
  rcases B with ⟨⟨bi, bb, bd⟩, scopeB, prefixB, literalsB, hooksB⟩
  rcases f with ⟨f, hi, hb, labels⟩
  change ((⟨String, scopeA.signature⟩ : Matching.SortMaps.Signature) ⟶
    (⟨String, scopeB.signature⟩ : Matching.SortMaps.Signature)) at f
  change f.sorts ai = bi at hi
  change f.sorts ab = bb at hb
  subst bi
  subst bb
  rfl

end SortMaps.Hom
end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
