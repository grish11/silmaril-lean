module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.LiteralProfiles.Defs

set_option backward.isDefEq.respectTransparency false
set_option linter.concreteInstances false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

private theorem attached_find_equal {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) (member : a ∈ xs) :
    xs.attach.find? (fun d => d.val == a) = some ⟨a, member⟩ := by
  cases found : xs.attach.find? (fun d => d.val == a) with
  | none =>
      have impossible := List.find?_eq_none.mp found ⟨a, member⟩ (List.mem_attach ..)
      simp at impossible
  | some d =>
      apply congrArg some
      have selected : d.val == a := List.find?_some (p := fun d : {x // x ∈ xs} => d.val == a) found
      exact Subtype.ext (beq_iff_eq.mp selected)

/-- A successful literal operation exposes the actual first selected binding. -/
theorem literalOperation_binding_find [sorts : SortBindings]
    {scope : Kore.Modules.Scope} {literals : List LiteralBinding} {literalPrefix : String}
    {mi : Nat} {l : Literal} {op : LiteralOperation scope literals literalPrefix mi l}
    (checked : literalOperation scope literals literalPrefix mi l = some op) :
    (literals.attach.find? (fun b => b.val.symbol.declaration == literalDeclaration literalPrefix mi l && b.val.literal == l)).map
      Subtype.val = some op.binding := by
  unfold literalOperation at checked
  obtain ⟨b, found, rest⟩ := Option.bind_eq_some_iff.mp checked
  split at rest
  next value =>
    obtain ⟨d, symbolFound, rest⟩ := Option.bind_eq_some_iff.mp rest
    split at rest
    next declared =>
      split at rest
      next profile =>
        rw [found]
        exact congrArg some (congrArg LiteralOperation.binding (Option.some.inj rest))
      next => simp at rest
    next => simp at rest
  next => simp at rest

private theorem literalOperation_selected [sorts : SortBindings]
    {scope : Kore.Modules.Scope} {literals : List LiteralBinding} {literalPrefix : String}
    {mi : Nat} {l : Literal} (b : {b // b ∈ literals})
    (found : literals.attach.find? (fun b => b.val.symbol.declaration == literalDeclaration literalPrefix mi l && b.val.literal == l) = some b)
    (declared : b.val.symbol ∈ scope.symbols) :
    ∃ op : LiteralOperation scope literals literalPrefix mi l,
      literalOperation scope literals literalPrefix mi l = some op ∧ op.binding = b.val := by
  have tests : b.val.symbol.declaration = literalDeclaration literalPrefix mi l ∧ b.val.literal = l := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using
      (List.find?_some (p := fun b : {b // b ∈ literals} =>
        b.val.symbol.declaration == literalDeclaration literalPrefix mi l && b.val.literal == l) found)
  obtain ⟨profile, value⟩ := tests
  unfold literalOperation
  rw [found]
  dsimp only [Bind.bind, Option.bind]
  split
  next value' =>
    rw [attached_find_equal scope.symbols b.val.symbol declared]
    dsimp only [Bind.bind, Option.bind]
    split
    next same => exact ⟨_, rfl, rfl⟩
    next absent => exact False.elim (absent rfl)
  next absent => exact False.elim (absent value)

/-- Literal lookup succeeds after a validated structural step and retains the
selected declaration, its origin and its actual literal value. Scope search may
choose a different position when sorts are identified; its value is fixed. -/
theorem Step.literalOperation_forward {A B : Package} (f : Step A B)
    (valid : literalProfiles A = true) {mi : Nat} {l : Literal}
    {op : @LiteralOperation A.base.bindings A.base.scope A.base.literals A.base.literalPrefix mi l}
    (checked : @literalOperation A.base.bindings A.base.scope A.base.literals A.base.literalPrefix mi l = some op) :
    ∃ op' : @LiteralOperation B.base.bindings B.base.scope B.base.literals B.base.literalPrefix mi l,
      @literalOperation B.base.bindings B.base.scope B.base.literals B.base.literalPrefix mi l = some op' ∧
      (@LiteralOperation.binding B.base.bindings _ _ _ _ _ op') = (⟨symbol f.semantic.native.sorts f.names (@LiteralOperation.binding A.base.bindings _ _ _ _ _ op).symbol, (@LiteralOperation.binding A.base.bindings _ _ _ _ _ op).literal⟩ : LiteralBinding) := by
  have first := literalOperation_binding_find (sorts := A.base.bindings) checked
  have remapped := congrArg (Option.map (fun b : LiteralBinding =>
    (⟨symbol f.semantic.native.sorts f.names b.symbol, b.literal⟩ : LiteralBinding))) first
  simp only [Option.map_map, Option.map_some] at remapped
  have mapped := (f.literal_find valid mi l).trans remapped
  cases targetFound : B.base.literals.attach.find? (fun b => b.val.symbol.declaration ==
      @literalDeclaration B.base.bindings B.base.literalPrefix mi l && b.val.literal == l) with
  | none => simp [targetFound] at mapped
  | some b =>
      have selected : b.val =
          (⟨symbol f.semantic.native.sorts f.names (@LiteralOperation.binding A.base.bindings _ _ _ _ _ op).symbol, (@LiteralOperation.binding A.base.bindings _ _ _ _ _ op).literal⟩ : LiteralBinding) := by
        simpa only [targetFound, Option.map_some, Option.some.injEq] using mapped
      have inScope : b.val.symbol ∈ B.base.scope.symbols := by
        rw [selected]
        have member := (f.semantic.native.operations (@LiteralOperation.operation A.base.bindings _ _ _ _ _ op)).property.1
        rw [f.operations, (@LiteralOperation.declared A.base.bindings _ _ _ _ _ op)] at member
        exact member
      obtain ⟨op', targetChecked, binding⟩ := literalOperation_selected (sorts := B.base.bindings) b targetFound inScope
      exact ⟨op', targetChecked, binding.trans selected⟩

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
