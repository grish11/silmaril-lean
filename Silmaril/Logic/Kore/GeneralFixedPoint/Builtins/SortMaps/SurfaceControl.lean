module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.AliasBridge

@[expose] public section
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.SurfaceControl
open CategoryTheory PopulatedControls RawControls

/-- Keep the two ordinary declarations and origins in the target, identifying
their sort names with Bool instead of dropping the declarations. -/
abbrev canonicalTarget : Signature :=
  { target with
    scope := { target.scope with
      sorts := source.scope.sorts.map (fun d => (d.1, aliasMap.native.sorts d.2)) } }

def semantic : source ⟶ canonicalTarget where
  native := aliasMap.native
  integer := aliasMap.integer
  boolean := aliasMap.boolean
  labels := aliasMap.labels

abbrev sourcePackage : Surface.Package := ⟨source, [closedAlias]⟩
abbrev targetPackage : Surface.Package := ⟨canonicalTarget, [closedAlias]⟩

/-- A populated actual structural step. The constraints are literal syntactic
identities, not assumed target checker success or satisfaction preservation. -/
def step : Surface.Step sourcePackage targetPackage where
  semantic := semantic
  names := id
  injective := Function.injective_id
  sortDeclarations := rfl
  symbolDeclarations := rfl
  legacyAliases := rfl
  aliasDeclarations := by
    change [closedAlias] = [Surface.renameAlias renameSort id closedAlias]
    simp [closedAlias, Surface.renameAlias, Surface.declaration, hookRaw, Surface.raw, renameSort]
  literalPrefix_eq := rfl
  literalDeclarations := rfl
  hookDeclarations := rfl
  literalNames _ _ := rfl
  operations := by
    intro n inputs output op
    rcases op with ⟨symbol, member, profile, output⟩
    simp only [Canonical.scope, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl

example : Surface.Path.action (.cons step (.nil targetPackage)) aliasRaw = aliasRaw := by
  change Surface.raw semantic.native.sorts id aliasRaw = aliasRaw
  simp [Surface.raw, aliasRaw]
example : step.semantic.native.sorts "CfgA" = step.semantic.native.sorts "CfgB" := by decide
example : step.semantic.native.sorts "SortInt" ≠ step.semantic.native.sorts "SortBool" := by decide

abbrev check := @Checking.elaborate canonicalTarget.bindings canonicalTarget.scope [closedAlias]
  canonicalTarget.literals canonicalTarget.literalPrefix 0 12 [] [] "SortBool" aliasRaw

theorem accepts : check.isSome = true := by decide +kernel
def typed := check.get accepts
theorem admitted : typed.admissible = true := by decide +kernel

theorem option_eq_some_get {α : Type} (o : Option α) (h : o.isSome = true) :
    o = some (o.get h) := by
  cases o <;> simp_all

def receipt : @CheckedSentence canonicalTarget.bindings canonicalTarget.scope
    canonicalTarget.literals canonicalTarget.literalPrefix where
  aliases := [closedAlias]
  moduleIndex := 0
  fuel := 12
  sets := []
  objects := []
  sort := "SortBool"
  raw := aliasRaw
  typed := typed
  accepted := option_eq_some_get check accepts
  admitted := admitted

theorem typed_eq_guard : typed = guard (context []) (context []) := by
  have computed : check = some (guard (context []) (context [])) :=
    elaborate_guard canonicalTarget.scope.sorts (by decide +kernel)
  unfold typed
  simp only [computed, Option.get_some]

theorem lower_guard : receipt.lower = guardSentence (context []) (context []) := by
  simp only [CheckedSentence.lower, receipt, typed_eq_guard, guardSentence]
  rfl

/-- The actual structural step has the actual lower/native square, with real
literal, hook and alias receipt calculations at both source and target. -/
theorem lower_native : receipt.lower =
    Matching.SortMaps.Hom.generalSentence step.semantic.native sourceReceipt.lower := by
  change receipt.lower = Matching.SortMaps.Hom.generalSentence aliasMap.native sourceReceipt.lower
  rw [lower_guard, source_lower_guard, general_guard_sentence]
  have empty : aliasMap.native.sorts ∘ context ([] : Names) = context ([] : Names) :=
    funext (fun i => i.elim0)
  exact congrArg₂ guardSentence empty.symm empty.symm

theorem source_square
    (M : @Model canonicalTarget.bindings canonicalTarget.scope canonicalTarget.literalPrefix
      canonicalTarget.literals canonicalTarget.hooks) :
    receipt.Satisfies M ↔ sourceReceipt.Satisfies (Hom.reduct step.semantic M) := by
  calc
    receipt.Satisfies M ↔ Matching.GeneralFixedPoint.Sentence.Satisfies M.native receipt.lower :=
      CheckedSentence.satisfies_lower M receipt
    _ ↔ Matching.GeneralFixedPoint.Sentence.Satisfies
        (Hom.reduct step.semantic M).native sourceReceipt.lower := by
      rw [lower_native, Hom.reduct_native]
      exact Matching.SortMaps.Hom.generalSatisfaction step.semantic.native M.native sourceReceipt.lower
    _ ↔ sourceReceipt.Satisfies (Hom.reduct step.semantic M) :=
      (CheckedSentence.satisfies_lower (Hom.reduct step.semantic M) sourceReceipt).symm

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.SurfaceControl
