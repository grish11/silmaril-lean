module

public import Silmaril.Logic.Kore.GeneralFixedPoint.BooleanRuntime.Syntax.Defs

-- Computed Boolean bindings intentionally coexist with the canonical fallback.
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.BooleanRuntime
open CategoryTheory Silmaril.Logic.Institution

/-- Text, located declarations, sort annotations, resolved bindings and actual
checked compilation are tied to successful computations, not supplied oracles. -/
structure Package where
  text : String
  source : Source
  parsed : Syntax.parse text = some source
  bindings : Builtins.SortBindings
  resolved : resolve source = some bindings
  binary : List HookBinding
  hooks_checked : hooks source bindings.boolSort = some binary
  checked : letI := bindings; Builtins.Checking.Package
  checked_input : checked.input = erase source

/-- The original visibility checker runs before generated literal declarations.
No declaration for the unused integer carrier index is added to the source. -/
def checkText (fuel : Nat) (text : String) : Option Package := do
  match parsed : Syntax.parse text with
  | none => none
  | some source =>
    match resolved : resolve source with
    | none => none
    | some bindings =>
      letI := bindings
      match hooked : hooks source bindings.boolSort with
      | none => none
      | some binary =>
        match checked : Builtins.Checking.checkDefinition fuel (erase source) with
        | none => none
        | some package =>
          have input : package.input = erase source := by
            unfold Builtins.Checking.checkDefinition at checked
            split at checked
            · contradiction
            · split at checked
              · contradiction
              · cases Option.some.inj checked
                rfl
          some ⟨text, source, parsed, bindings, resolved, binary, hooked, package, input⟩

/-- Additional Boolean graph laws remain a named dependent predicate so model
transport rewrites its indices before unfolding operation projections. -/
def BinaryLaws [sorts : Builtins.SortBindings] {scope : Kore.Modules.Scope}
    {literalPrefix : String} {literals : List Builtins.LiteralBinding} {notHooks : List Builtins.HookBinding}
    (binary : List HookBinding) (base : Builtins.Model scope literalPrefix literals notHooks) : Prop :=
  ∀ b ∈ binary,
    ∀ (op : scope.signature.operations 2 (fun _ => sorts.boolSort) sorts.boolSort),
    op.val = b.symbol → ∀ args,
    base.native.operation op args = Set.singleton (base.carriers.boolean.symm
      (b.hook.eval (base.carriers.boolean (args 0)) (base.carriers.boolean (args 1))))

/-- All semantic indices are parameters of one model structure. Rewriting a
checked package transports the model and its graph proofs together. -/
structure ModelData [Builtins.SortBindings] (scope : Kore.Modules.Scope)
    (literalPrefix : String) (literals : List Builtins.LiteralBinding)
    (notHooks : List Builtins.HookBinding) (binary : List HookBinding) where
  base : Builtins.Model scope literalPrefix literals notHooks
  binary : BinaryLaws binary base

namespace Package
abbrev CheckedModule (p : Package) :=
  letI := p.bindings
  Builtins.Checking.CheckedModule p.checked.checked

/-- Extra graphs constrain every actual Boolean argument tuple, including those
not denoted by literal text. The existing base supplies exact literal/not laws.
hasDomainValues is witnessed by the Bool carrier equivalence, not ignored. -/
abbrev Model (p : Package) :=
  letI := p.bindings
  ModelData p.checked.checked.native.ambient p.checked.checked.literalPrefix
    p.checked.checked.literals p.checked.checked.hooks p.binary

instance (p : Package) : letI := p.bindings; Category p.Model := by
  letI := p.bindings
  exact {
    Hom := fun M N => M.base.native ⟶ N.base.native
    id := fun M => 𝟙 M.base.native
    comp := fun f g => f ≫ g
    id_comp := fun f => Category.id_comp f
    comp_id := fun f => Category.comp_id f
    assoc := fun f g h => Category.assoc f g h }

/-- Every Boolean carrier element is denoted by a canonical domain value.
This follows from the Boolean carrier equivalence independently of generated
literal-operation names and compiler output. -/
theorem domainValues_total (p : Package) : letI := p.bindings;
    ∀ (M : p.Model) (x : M.base.native.carrier p.bindings.boolSort),
    ∃ b : Bool, M.base.carriers.boolean.symm b = x := by
  let : Builtins.SortBindings := p.bindings
  intro M x
  exact ⟨M.base.carriers.boolean x, M.base.carriers.boolean.symm_apply_apply x⟩

theorem domainValues_distinct (p : Package) : letI := p.bindings;
    ∀ M : p.Model,
    M.base.carriers.boolean.symm true ≠ M.base.carriers.boolean.symm false := by
  let : Builtins.SortBindings := p.bindings
  intro M h
  have := M.base.carriers.boolean.symm.injective h
  contradiction

/-- The retained domain-value annotation covers the carrier through the actual
independent raw interpreter: each element is denoted by a canonical text. -/
theorem domainValues_denote_total (p : Package) : letI := p.bindings;
    ∀ (M : p.Model) (x : M.base.native.carrier p.bindings.boolSort), ∃ text : String,
      Builtins.Semantics.denote p.checked.checked.native.ambient [] M.base.native M.base.carriers
        1 [] [] p.bindings.boolSort (.domainValue p.bindings.boolSort text) = some {x} := by
  let : Builtins.SortBindings := p.bindings
  intro M x
  obtain ⟨b, hx⟩ := p.domainValues_total M x
  rw [← hx]
  have different : Builtins.SortBindings.boolSort ≠ Builtins.SortBindings.intSort :=
    Ne.symm p.bindings.distinct
  cases b
  · refine ⟨"false", ?_⟩
    simp [Builtins.Semantics.denote, Builtins.Literal.parse, different,
      Builtins.Carriers.literal, Builtins.Literal.sort]
    rfl
  · refine ⟨"true", ?_⟩
    simp [Builtins.Semantics.denote, Builtins.Literal.parse, different,
      Builtins.Carriers.literal, Builtins.Literal.sort]
    rfl

/-- Adequacy still compares the independent raw interpreter of the unchanged
original pattern with its actual typed compilation. Binary hook laws restrict
models; no compiler-output semantics defines the raw side. -/
theorem satisfies_lower (p : Package) (M : p.Model)
    (q : letI := p.bindings; Builtins.CheckedSentence p.checked.checked.native.ambient
      p.checked.checked.literals p.checked.checked.literalPrefix) :
    letI := p.bindings
    q.Satisfies M.base ↔ Matching.GeneralFixedPoint.Sentence.Satisfies M.base.native q.lower := by
  let : Builtins.SortBindings := p.bindings
  exact q.satisfies_lower M.base

theorem models_native_iff (p : Package) (m : p.CheckedModule) (M : p.Model) :
    letI := p.bindings
    (∀ q ∈ m.axiomSet, q.Satisfies M.base) ↔
      (∀ q ∈ m.nativeAxiomSet, Matching.GeneralFixedPoint.Sentence.Satisfies M.base.native q) := by
  let : Builtins.SortBindings := p.bindings
  exact m.models_native_iff M.base

theorem satisfiable_native_iff (p : Package) (m : p.CheckedModule) :
    letI := p.bindings
    (∃ M : p.Model, ∀ q ∈ m.axiomSet, q.Satisfies M.base) ↔
      (∃ M : p.Model, ∀ q ∈ m.nativeAxiomSet,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.base.native q) := by
  let : Builtins.SortBindings := p.bindings
  exact exists_congr (fun M => p.models_native_iff m M)

theorem entails_native_iff (p : Package) (m : p.CheckedModule)
    (q : letI := p.bindings; Builtins.CheckedSentence p.checked.checked.native.ambient
      p.checked.checked.literals p.checked.checked.literalPrefix) :
    letI := p.bindings
    (∀ M : p.Model, (∀ a ∈ m.axiomSet, a.Satisfies M.base) → q.Satisfies M.base) ↔
      (∀ M : p.Model, (∀ a ∈ m.nativeAxiomSet,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.base.native a) →
        Matching.GeneralFixedPoint.Sentence.Satisfies M.base.native q.lower) := by
  let : Builtins.SortBindings := p.bindings
  constructor
  · intro h M hm
    exact (p.satisfies_lower M q).mp (h M ((p.models_native_iff m M).mpr hm))
  · intro h M hm
    exact (p.satisfies_lower M q).mpr (h M ((p.models_native_iff m M).mp hm))
/-- Source room restricted by all Boolean laws, retaining actual native model
homomorphisms. Both ends quantify over the same complete restricted models. -/
def sourceRoom (p : Package) : letI := p.bindings; Room := by
  letI := p.bindings
  exact ⟨Builtins.CheckedSentence p.checked.checked.native.ambient
    p.checked.checked.literals p.checked.checked.literalPrefix,
    Cat.of p.Model, fun M q => q.Satisfies M.base⟩

def nativeRoom (p : Package) : letI := p.bindings; Room := by
  letI := p.bindings
  exact ⟨Matching.GeneralFixedPoint.Sentence p.checked.checked.native.ambient.signature,
    Cat.of p.Model, fun M q => Matching.GeneralFixedPoint.Sentence.Satisfies M.base.native q⟩

def loweringCorridor (p : Package) : letI := p.bindings;
    Corridor p.sourceRoom p.nativeRoom := by
  letI := p.bindings
  exact ⟨Builtins.CheckedSentence.lower, 𝟭 _, fun M q => (p.satisfies_lower M q).symm⟩

theorem lowering_modelExpansive (p : Package) : letI := p.bindings;
    p.loweringCorridor.ModelExpansive := by
  let : Builtins.SortBindings := p.bindings
  exact fun M => ⟨M, rfl⟩

end Package
end Silmaril.Logic.Kore.GeneralFixedPoint.BooleanRuntime
