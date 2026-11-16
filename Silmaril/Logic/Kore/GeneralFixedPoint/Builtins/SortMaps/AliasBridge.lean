module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.RawControls

@[expose] public section
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.RawControls
open CategoryTheory PopulatedControls

/-- A concrete closed typed skeleton, polymorphic in its otherwise unused
contexts. Every operation is the actual retained canonical declaration. -/
def guard {r k : Nat} (P : Fin r → String) (Γ : Fin k → String) :
    Matching.GeneralFixedPoint.Pattern Canonical.scope.signature P Γ "SortBool" :=
  .app Canonical.negationOp
    (Fin.cases
      (.app Canonical.equalityOp
        (Fin.cases (.app zeroOp (fun i => i.elim0))
          (Fin.cases (.app zeroOp (fun i => i.elim0)) (fun i => i.elim0))))
      (fun i => i.elim0))

/-- The controls vary the declared sort list while retaining the actual six
canonical symbol declarations. The typed signature depends on those symbols. -/
def guardScope (sorts : List (Kore.Modules.Origin × String)) : Kore.Modules.Scope :=
  { Canonical.scope with sorts := sorts }

private theorem zero_read : decimalInteger "0" = some (0 : Int) := by decide +kernel

private theorem canonical_integer_sort :
    @SortBindings.intSort canonicalSortBindings = "SortInt" := rfl

private theorem guard_bind_some {α β : Type} (a : α) (f : α → Option β) :
    (do let x ← some a; f x) = f a := rfl

private theorem find_guard_alias (sorts : List (Kore.Modules.Origin × String)) :
    (guardScope sorts).symbols.attach.find?
    (fun d => d.val.declaration.name == "zeroIsNotZero") = none := by
  change Canonical.scope.symbols.attach.find?
    (fun d => d.val.declaration.name == "zeroIsNotZero") = none
  decide +kernel

private theorem find_closed_alias : [closedAlias].find?
    (fun d => d.symbol.name == "zeroIsNotZero") = some closedAlias := rfl

private theorem find_guard_negation (sorts : List (Kore.Modules.Origin × String)) :
    (guardScope sorts).symbols.attach.find?
    (fun d => d.val.declaration.name == "notBool") =
      some ⟨Canonical.negation, by simp [guardScope, Canonical.scope]⟩ := by
  change Canonical.scope.symbols.attach.find?
    (fun d => d.val.declaration.name == "notBool") =
      some ⟨Canonical.negation, by simp [Canonical.scope]⟩
  decide +kernel

private theorem find_guard_equality (sorts : List (Kore.Modules.Origin × String)) :
    (guardScope sorts).symbols.attach.find?
    (fun d => d.val.declaration.name == "eqInt") =
      some ⟨Canonical.equality, by simp [guardScope, Canonical.scope]⟩ := by
  change Canonical.scope.symbols.attach.find?
    (fun d => d.val.declaration.name == "eqInt") =
      some ⟨Canonical.equality, by simp [Canonical.scope]⟩
  decide +kernel

private theorem find_zero_binding : Canonical.literals.attach.find?
    (fun b => b.val.symbol.declaration ==
      literalDeclaration Canonical.literalPrefix 0 (.integer 0) && b.val.literal == .integer 0) =
      some ⟨Canonical.zero, by simp [Canonical.literals]⟩ := by decide +kernel

private theorem find_zero_symbol (sorts : List (Kore.Modules.Origin × String)) :
    (guardScope sorts).symbols.attach.find?
    (fun d => d.val == Canonical.zero.symbol) =
      some ⟨Canonical.zero.symbol, by simp [guardScope, Canonical.scope]⟩ := by
  change Canonical.scope.symbols.attach.find?
    (fun d => d.val == Canonical.zero.symbol) =
      some ⟨Canonical.zero.symbol, by simp [Canonical.scope]⟩
  decide +kernel

private theorem zero_literal_operation (sorts : List (Kore.Modules.Origin × String)) :
    literalOperation (guardScope sorts) Canonical.literals Canonical.literalPrefix 0 (.integer 0) =
      some ⟨Canonical.zero, by simp [Canonical.literals], rfl, zeroOp, rfl⟩ := by
  simp only [literalOperation, find_zero_binding, guard_bind_some, find_zero_symbol]
  simp only [Canonical.zero, eq_self, dite_true]
  rfl

/-- Elaborated finite profiles can use list lookup functions instead of the
constant profiles of the independently written skeleton. Compare those
profiles extensionally while retaining the actual operation declaration. -/
theorem app_ext {scope : Kore.Modules.Scope} {r k n : Nat}
    {P : Fin r → String} {Γ : Fin k → String} {s : String}
    {inputs inputs' : Fin n → String}
    {op : scope.signature.operations n inputs s}
    {op' : scope.signature.operations n inputs' s}
    {args : ∀ i, Matching.GeneralFixedPoint.Pattern scope.signature P Γ (inputs i)}
    {args' : ∀ i, Matching.GeneralFixedPoint.Pattern scope.signature P Γ (inputs' i)}
    (profile : inputs = inputs') (same : op.val = op'.val)
    (values : ∀ i, HEq (args i) (args' i)) :
    Matching.GeneralFixedPoint.Pattern.app op args =
      Matching.GeneralFixedPoint.Pattern.app op' args' := by
  subst inputs'
  have ops : op = op' := Subtype.ext same
  subst op'
  apply congrArg (Matching.GeneralFixedPoint.Pattern.app op)
  funext i
  exact eq_of_heq (values i)

/-- Compute this concrete alias with the actual checker. Its only variable
metadata is the declared sort list; Bool must be declared in that list. Lookup
and literal-read equations keep the generated literal prefix opaque. -/
theorem elaborate_guard (sorts : List (Kore.Modules.Origin × String))
    (declaredBool : Kore.Modules.Checking.namedSort (guardScope sorts) "SortBool" = true) :
    @Checking.elaborate canonicalSortBindings (guardScope sorts) [closedAlias]
      Canonical.literals Canonical.literalPrefix 0 12 [] [] "SortBool" aliasRaw =
      some (guard (context []) (context [])) := by
  have valid : closedAlias.valid (guardScope sorts) = true := by
    simpa [Alias.valid, Aliases.Declaration.valid, closedAlias] using declaredBool
  simp only [aliasRaw, Checking.elaborate, find_guard_alias, find_closed_alias,
    guard_bind_some, valid]
  simp [closedAlias, hookRaw, Checking.elaborate, find_guard_negation, find_guard_equality,
    Canonical.negation, Canonical.equality, guard_bind_some,
    Literal.parse, canonical_integer_sort, zero_read, zero_literal_operation, Literal.sort,
    Kore.Modules.Checking.collect, Alias.names, Aliases.Declaration.names,
    Matching.GeneralFixedPoint.Pattern.substitute]
  unfold guard
  apply app_ext (scope := guardScope sorts)
  · funext i
    fin_cases i
    rfl
  · rfl
  · intro i
    fin_cases i
    apply heq_of_eq
    apply app_ext (scope := guardScope sorts)
    · funext j; fin_cases j <;> rfl
    · rfl
    · intro j
      fin_cases j
      all_goals
        apply heq_of_eq
        apply app_ext (scope := guardScope sorts)
        · funext k; exact k.elim0
        · rfl
        · intro k; exact k.elim0

/-- Actual source alias elaboration equals the independently written typed
hook/literal skeleton. No successful-checker equation is an input premise. -/
theorem sourceTyped_eq_guard : sourceTyped = guard (context []) (context []) := by
  have computed : sourceCheck = some (guard (context []) (context [])) :=
    elaborate_guard source.scope.sorts (by decide +kernel)
  unfold sourceTyped
  simp only [computed, Option.get_some]

theorem targetTyped_eq_guard : targetTyped = guard (context []) (context []) := by
  have computed : targetCheck = some (guard (context []) (context [])) :=
    elaborate_guard target.scope.sorts (by decide +kernel)
  unfold targetTyped
  simp only [computed, Option.get_some]

/-- Nullary input profiles are equal extensionally. This proves actual
application equality even when native sort mapping changes the phantom
Fin 0 profile function; no generic type-cast invariance is assumed. -/
private theorem nullary_app_eq {scope : Kore.Modules.Scope} {r k : Nat}
    {P : Fin r → String} {Γ : Fin k → String} {s : String}
    {inputs inputs' : Fin 0 → String}
    (op : scope.signature.operations 0 inputs s)
    (op' : scope.signature.operations 0 inputs' s)
    (same : op.val = op'.val)
    (args : ∀ i, Matching.GeneralFixedPoint.Pattern scope.signature P Γ (inputs i))
    (args' : ∀ i, Matching.GeneralFixedPoint.Pattern scope.signature P Γ (inputs' i)) :
    Matching.GeneralFixedPoint.Pattern.app op args =
      Matching.GeneralFixedPoint.Pattern.app op' args' := by
  have profile : inputs = inputs' := funext (fun i => i.elim0)
  subst inputs'
  have ops : op = op' := Subtype.ext same
  subst op'
  have values : args = args' := funext (fun i => i.elim0)
  subst args'
  rfl

/-- Full native sort reindexing of the real hook/literal skeleton. Contexts
and their sort maps remain explicit, including the empty-profile seam. -/
theorem general_guard {r k : Nat} (P : Fin r → String) (Γ : Fin k → String) :
    Matching.SortMaps.Hom.generalPattern aliasMap.native (guard P Γ) =
      guard (aliasMap.native.sorts ∘ P) (aliasMap.native.sorts ∘ Γ) := by
  change Matching.GeneralFixedPoint.Pattern.app Canonical.negationOp _ = _
  apply congrArg (Matching.GeneralFixedPoint.Pattern.app Canonical.negationOp)
  funext i
  fin_cases i
  change Matching.GeneralFixedPoint.Pattern.app Canonical.equalityOp _ = _
  apply congrArg (Matching.GeneralFixedPoint.Pattern.app Canonical.equalityOp)
  funext j
  fin_cases j
  all_goals apply nullary_app_eq
  all_goals rfl

def guardSentence (P Γ : Fin 0 → String) :
    Matching.GeneralFixedPoint.Sentence Canonical.scope.signature :=
  ⟨0, 0, P, Γ, "SortBool", guard P Γ, rfl⟩

theorem source_lower_guard : sourceReceipt.lower = guardSentence (context []) (context []) := by
  simp only [CheckedSentence.lower, sourceReceipt, sourceTyped_eq_guard, guardSentence]
  rfl

theorem target_lower_guard : targetReceipt.lower = guardSentence (context []) (context []) := by
  simp only [CheckedSentence.lower, targetReceipt, targetTyped_eq_guard, guardSentence]
  rfl

theorem general_guard_sentence (P Γ : Fin 0 → String) :
    Matching.SortMaps.Hom.generalSentence aliasMap.native (guardSentence P Γ) =
      guardSentence (aliasMap.native.sorts ∘ P) (aliasMap.native.sorts ∘ Γ) := by
  simp only [Matching.SortMaps.Hom.generalSentence, guardSentence, general_guard]
  rfl

/-- Actual lowering/native equality for a raw alias containing both hooks and
literal syntax, through a noninjective ordinary-sort map. Both source receipts
come from independent actual checker computations in RawControls. -/
theorem alias_lower_native : targetReceipt.lower =
    Matching.SortMaps.Hom.generalSentence aliasMap.native sourceReceipt.lower := by
  rw [source_lower_guard, target_lower_guard, general_guard_sentence]
  have empty : aliasMap.native.sorts ∘ context ([] : Names) = context ([] : Names) :=
    funext (fun i => i.elim0)
  exact congrArg₂ guardSentence empty.symm empty.symm

/-- The raw-source square now follows from the independently proved lower and
native satisfaction theorems, rather than comparing two unrelated receipts. -/
theorem alias_source_square
    (M : @Model target.bindings target.scope target.literalPrefix target.literals target.hooks) :
    targetReceipt.Satisfies M ↔ sourceReceipt.Satisfies (Hom.reduct aliasMap M) := by
  calc
    targetReceipt.Satisfies M ↔
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native targetReceipt.lower :=
      CheckedSentence.satisfies_lower M targetReceipt
    _ ↔ Matching.GeneralFixedPoint.Sentence.Satisfies
        (Hom.reduct aliasMap M).native sourceReceipt.lower := by
      rw [alias_lower_native, Hom.reduct_native]
      exact Matching.SortMaps.Hom.generalSatisfaction aliasMap.native M.native sourceReceipt.lower
    _ ↔ sourceReceipt.Satisfies (Hom.reduct aliasMap M) :=
      (CheckedSentence.satisfies_lower (Hom.reduct aliasMap M) sourceReceipt).symm

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.RawControls
