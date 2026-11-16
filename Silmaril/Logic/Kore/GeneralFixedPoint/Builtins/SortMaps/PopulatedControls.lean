module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Models
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Modules.Canonical

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.PopulatedControls
open CategoryTheory

abbrev source : Signature where
  bindings := canonicalSortBindings
  scope := { Canonical.scope with sorts :=
    (⟨"CONTROL", 0⟩, "CfgA") :: (⟨"CONTROL", 1⟩, "CfgB") :: Canonical.scope.sorts }
  literalPrefix := Canonical.literalPrefix
  literals := Canonical.literals
  hooks := Canonical.hooks

abbrev target : Signature where
  bindings := canonicalSortBindings
  scope := Canonical.scope
  literalPrefix := Canonical.literalPrefix
  literals := Canonical.literals
  hooks := Canonical.hooks

def renameSort (s : String) : String :=
  if s = "SortInt" then "SortInt" else "SortBool"

theorem profiles_fixed (symbol : Kore.Modules.NamedSymbol)
    (member : symbol ∈ Canonical.scope.symbols) :
    symbol.declaration.arguments.map renameSort = symbol.declaration.arguments ∧
      renameSort symbol.declaration.result = symbol.declaration.result := by
  simp only [Canonical.scope, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

/-- Native operation transport retains each actual declaration value. -/
def nativeMap : source.native ⟶ target.native where
  sorts := renameSort
  operations := by
    intro n inputs output op
    have fixed := profiles_fixed op.val op.property.1
    refine ⟨op.val, op.property.1, ?_, ?_⟩
    · calc
        op.val.declaration.arguments = op.val.declaration.arguments.map renameSort := fixed.1.symm
        _ = (List.ofFn inputs).map renameSort := congrArg (List.map renameSort) op.property.2.1
        _ = List.ofFn (renameSort ∘ inputs) := by simp [List.map_ofFn, Function.comp_def]
    · exact fixed.2.symm.trans (congrArg renameSort op.property.2.2)

/-- Retains all six actual canonical operations and their actual declaration
identities while identifying two ordinary declared sort names with Bool. -/
def aliasMap : source ⟶ target where
  native := nativeMap
  integer := by decide
  boolean := by decide
  labels op _ member := member

example : aliasMap.native.sorts "CfgA" = aliasMap.native.sorts "CfgB" := by decide
example : aliasMap.native.sorts "CfgA" = "SortBool" := by decide
example : ¬ ∃ f : source ⟶ target,
    f.native.sorts "SortInt" = f.native.sorts "SortBool" := by
  rintro ⟨f, collapsed⟩
  exact f.builtin_images_distinct collapsed

/-- This is the actual populated retained model, not an assumed law package. -/
def model : @Model source.bindings source.scope source.literalPrefix source.literals source.hooks :=
  aliasMap.reduct Canonical.model

/-- Every literal binding and both hook laws are discharged by the constructed
restricted reduct. These generic controls range over every actual argument. -/
theorem all_literal_laws (b : LiteralBinding) (member : b ∈ source.literals)
    (l : Literal) (value : b.literal = l)
    (op : source.scope.signature.operations 0 (fun i => i.elim0) l.sort)
    (identity : op.val = b.symbol) :
    model.native.operation op (fun i => i.elim0) = {model.carriers.literal l} :=
  model.laws.literal b member l value op identity

theorem all_intEq_laws (b : HookBinding) (member : b ∈ source.hooks)
    (hook : b.hook = .intEq)
    (op : source.scope.signature.operations 2 (fun _ => "SortInt") "SortBool")
    (identity : op.val = b.symbol) (args : ∀ _i : Fin 2, model.native.carrier ("SortInt" : String)) :
    model.native.operation op args =
      {model.carriers.boolean.symm (Operational.Conditional.intEqual
        (model.carriers.integer (args 0)) (model.carriers.integer (args 1)))} :=
  model.laws.intEq b member hook op identity args

theorem all_boolNot_laws (b : HookBinding) (member : b ∈ source.hooks)
    (hook : b.hook = .boolNot)
    (op : source.scope.signature.operations 1 (fun _ => "SortBool") "SortBool")
    (identity : op.val = b.symbol) (args : ∀ _i : Fin 1, model.native.carrier ("SortBool" : String)) :
    model.native.operation op args = {model.carriers.boolean.symm (!(model.carriers.boolean (args 0)))} :=
  model.laws.boolNot b member hook op identity args

def zeroOp : source.scope.signature.operations 0 (fun i => i.elim0) "SortInt" :=
  ⟨Canonical.zero.symbol, by simp [Canonical.scope], rfl, rfl⟩

theorem literal_zero : model.native.operation zeroOp (fun i => i.elim0) =
    {model.carriers.integer.symm 0} :=
  model.laws.literal Canonical.zero (by simp [Canonical.literals])
    (.integer 0) rfl zeroOp rfl

abbrev erasedHooks : Signature := { target with hooks := [] }
abbrev erasedLiterals : Signature := { target with literals := [] }

/-- The populated source forbids silently dropping its actual hook laws. -/
theorem cannot_erase_hooks : ¬ Nonempty (source ⟶ erasedHooks) := by
  rintro ⟨f⟩
  have mark : Label.hook .intEq ∈ source.labels Canonical.equality :=
    ⟨⟨Canonical.equality, .intEq⟩, by simp [Canonical.hooks], rfl, rfl⟩
  have retained := f.labels Canonical.equalityOp mark
  change ∃ b ∈ ([] : List HookBinding), _ at retained
  simp at retained

/-- Literal constraints cannot disappear from an admitted populated map. -/
theorem cannot_erase_literals : ¬ Nonempty (source ⟶ erasedLiterals) := by
  rintro ⟨f⟩
  have mark : Label.literal (.integer 0) ∈ source.labels Canonical.zero.symbol :=
    ⟨Canonical.zero, by simp [Canonical.literals], rfl, rfl⟩
  have retained := f.labels zeroOp mark
  change ∃ b ∈ ([] : List LiteralBinding), _ at retained
  simp at retained

/-- Concrete computations of both hook laws on actual retained declarations. -/
theorem equality_on_zero :
    model.native.operation Canonical.equalityOp
      (fun _ => model.carriers.integer.symm 0) = {model.carriers.boolean.symm true} := by
  have law := model.laws.intEq ⟨Canonical.equality, .intEq⟩
    (by simp [Canonical.hooks]) rfl Canonical.equalityOp rfl
    (fun _ => model.carriers.integer.symm 0)
  simpa [Operational.Conditional.intEqual] using law

theorem negation_on_true :
    model.native.operation Canonical.negationOp
      (fun _ => model.carriers.boolean.symm true) = {model.carriers.boolean.symm false} := by
  simpa only [Equiv.apply_symm_apply, Bool.not_true] using
    model.laws.boolNot ⟨Canonical.negation, .boolNot⟩
      (by simp [Canonical.hooks]) rfl Canonical.negationOp rfl
      (fun _ => model.carriers.boolean.symm true)

/-- Explicit population controls: empty-list proofs cannot establish these. -/
example : Canonical.zero ∈ source.literals := by simp [Canonical.literals]
example : (⟨Canonical.equality, .intEq⟩ : HookBinding) ∈ source.hooks := by simp [Canonical.hooks]
example : (⟨Canonical.negation, .boolNot⟩ : HookBinding) ∈ source.hooks := by simp [Canonical.hooks]

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.PopulatedControls
