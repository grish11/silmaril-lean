module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.LiteralProfiles.Defs
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Modules.Defs

set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

/-- Every literal binding produced by the actual lowering procedure has the
profile checked by literalProfiles, for either visibility-checking mode. -/
theorem lowerModule_literal_profiles [bindings : SortBindings]
    (literalPrefix : String) (mi fuel : Nat) (skeleton : Bool)
    (source : Aliases.SourceModule) (lowered : LoweredModule)
    (accepted : lowerModule literalPrefix mi fuel skeleton source = some lowered) :
    ∀ b ∈ lowered.literals, b.symbol.declaration.arguments = [] ∧
      b.symbol.declaration.result = @Literal.sort bindings b.literal := by
  unfold lowerModule at accepted
  dsimp only [bind, Option.bind] at accepted
  split at accepted
  · contradiction
  · dsimp only at accepted
    split at accepted
    · contradiction
    · cases Option.some.inj accepted
      intro b member
      rcases List.mem_map.mp member with ⟨pair, _, rfl⟩
      exact ⟨rfl, rfl⟩

private theorem mapM_member {α β : Type} (f : α → Option β) (xs : List α)
    {ys : List β} {y : β} (accepted : xs.mapM f = some ys) (member : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
      change some [] = some ys at accepted
      cases Option.some.inj accepted
      contradiction
  | cons x xs ih =>
      cases head : f x with
      | none => simp [head] at accepted
      | some z =>
          cases tail : xs.mapM f with
          | none => simp [head, tail] at accepted
          | some rest =>
              have same : z :: rest = ys := by simpa [head, tail] using accepted
              subst ys
              rcases List.mem_cons.mp member with same | inRest
              · subst z
                exact ⟨x, List.mem_cons_self, head⟩
              · obtain ⟨w, sourceMember, checked⟩ := ih tail inRest
                exact ⟨w, List.mem_cons_of_mem x sourceMember, checked⟩

/-- The package uses the actual ambient declaration scope and the actual
literal, hook and alias lists retained by a successful source definition. -/
def checkedSource [bindings : SortBindings] (d : CheckedDefinition) : Package :=
  ⟨⟨bindings, d.native.ambient, d.literalPrefix, d.literals, d.hooks⟩, d.aliases⟩

/-- The finite profile validator accepts every output of actual source
lowering. Callers do not need to supply a separate profile assumption for
definitions obtained through the checked source API. -/
theorem checkedSource_literalProfiles [bindings : SortBindings] (d : CheckedDefinition) :
    literalProfiles (checkedSource d) = true := by
  apply List.all_eq_true.mpr
  intro b member
  change b ∈ d.lowered.flatMap LoweredModule.literals at member
  obtain ⟨lowered, inLowered, bindingMember⟩ := List.mem_flatMap.mp member
  obtain ⟨⟨source, mi⟩, _, loweredChecked⟩ :=
    mapM_member _ _ d.lowered_checked inLowered
  obtain ⟨arguments, result⟩ := lowerModule_literal_profiles
    d.literalPrefix mi d.fuel false source lowered loweredChecked b bindingMember
  change (b.symbol.declaration.arguments.isEmpty &&
    b.symbol.declaration.result == @Literal.sort bindings b.literal) = true
  simp only [arguments, result, List.isEmpty_nil, beq_self_eq_true, Bool.and_self]

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
