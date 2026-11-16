module

public import Silmaril.Logic.Kore.Modules.Theory.Thms

/-! Manually authored actual KORE text, exercising the general module frontend.
These are not observations of the K backend or claims about arbitrary K sources. -/
@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Examples
open Checking
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Arbitrary-arity symbols, forward local references, binders, aliases and a diamond. -/
def source : String := "[]
module BASE
  axiom{} \\top{S{}}() []
  symbol triple{}(S{},S{},S{}):S{} []
  sort S{} []
endmodule []
module LEFT
  import BASE []
  alias hold{}(S{}):S{} where hold{}(X:S{}):=\\exists{S{}}(Y:S{},X:S{}) []
  axiom{} \\forall{S{}}(X:S{},\\iff{S{}}(X:S{},X:S{})) []
endmodule []
module RIGHT
  import BASE []
  axiom{} \\top{S{}}() []
endmodule []
module JOIN
  import LEFT []
  import RIGHT []
  claim{} \\forall{S{}}(Y:S{},\\iff{S{}}(hold{}(Y:S{}),Y:S{})) []
  claim{} \\bottom{S{}}() []
  claim{} \\forall{S{}}(X:S{},triple{}(X:S{},X:S{},X:S{})) []
endmodule []"

theorem checked_source : (checkText 64 source).isSome = true := by decide +kernel

def checked : CheckedDefinition := (checkText 64 source).get (by exact checked_source)
def base : CheckedModule checked.ambient := checked.modules.get ⟨0, by decide +kernel⟩
def left : CheckedModule checked.ambient := checked.modules.get ⟨1, by decide +kernel⟩
def right : CheckedModule checked.ambient := checked.modules.get ⟨2, by decide +kernel⟩
def join : CheckedModule checked.ambient := checked.modules.get ⟨3, by decide +kernel⟩

theorem diamond_one_symbol : join.scope.symbols.length = 1 := by decide +kernel
theorem diamond_same_origin : (join.axioms.map CheckedSentence.origin) =
    [⟨"LEFT", 2⟩, ⟨"BASE", 0⟩, ⟨"RIGHT", 1⟩, ⟨"BASE", 0⟩] := by decide +kernel
theorem claims_are_separate : join.localAxioms.length = 0 ∧ join.claims.length = 3 := by decide +kernel

def captureClaim : FirstOrder.Sentence checked.ambient.signature :=
  (join.claims.get ⟨0, by decide +kernel⟩).sentence

/-- The inner Y binder leaves the alias argument at index1, proving capture avoidance. -/
theorem capture_exact : captureClaim.pattern =
    .forall "S" (.iff (.exists "S" (.evar 1)) (.evar 0)) := by rfl

/-- A nontrivial two-element model distinguishes capture from accidental rebinding. -/
def model : Matching.FirstOrder.Model checked.ambient.signature where
  carrier _ := Bool
  nonempty _ := ⟨false⟩
  operation _ _ := Set.univ

theorem capture_claim_true : FirstOrder.Sentence.Satisfies model captureClaim := by
  change ∀ (_ : Fin 0 → Bool) (result : Bool),
    ∀ y : Bool, ((∃ _ : Bool, result = y) ↔ result = y)
  simp

/-- The actual compiled claim follows for every model, not only the Bool witness. -/
theorem capture_claim_proved : join.Proves captureClaim := by
  intro M _
  change FirstOrder.Sentence.Satisfies M captureClaim
  intro v result
  change ∀ y : M.carrier "S", ((∃ _ : M.carrier "S", result = y) ↔ result = y)
  intro y
  rcases M.nonempty "S" with ⟨witness⟩
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨witness, h⟩⟩

def falseClaim : FirstOrder.Sentence checked.ambient.signature :=
  (join.claims.get ⟨1, by decide +kernel⟩).sentence

theorem false_claim_false : ¬ FirstOrder.Sentence.Satisfies model falseClaim := by
  intro h
  exact h (fun i => Fin.elim0 i) false

/-- The concrete model satisfies all actual transitively imported axioms. -/
theorem model_satisfies_join : ∀ p ∈ join.axiomSet, FirstOrder.Sentence.Satisfies model p := by
  intro p hp
  rcases hp with ⟨d, hd, rfl⟩
  change d ∈ [_, _, _, _] at hd
  cases hd with
  | head =>
      change ∀ (_ : Fin 0 → Bool) (result : Bool), ∀ x : Bool, (result = x ↔ result = x)
      intros; rfl
  | tail _ hd =>
      cases hd with
      | head =>
          change ∀ (_ : Fin 0 → Bool) (_ : Bool), True
          intros; trivial
      | tail _ hd =>
          cases hd with
          | head =>
              change ∀ (_ : Fin 0 → Bool) (_ : Bool), True
              intros; trivial
          | tail _ hd =>
              cases hd with
              | head =>
                  change ∀ (_ : Fin 0 → Bool) (_ : Bool), True
                  intros; trivial
              | tail _ hd => cases hd

theorem false_claim_not_proved : ¬ join.Proves falseClaim := by
  intro h
  exact false_claim_false (h model model_satisfies_join)

def minimal (body : String) : String := "[] module M " ++ body ++ " endmodule []"

theorem heterogeneous_symbol_checked :
    (checkText 32 (minimal "sort S{} [] sort T{} [] symbol pair{}(S{},T{}):S{} [] claim{} pair{}(X:S{},Y:T{}) []")).isSome = true := by decide +kernel

theorem forward_alias_checked :
    (checkText 32 (minimal "sort S{} [] alias first{}(S{}):S{} where first{}(X:S{}):=second{}(X:S{}) [] alias second{}(S{}):S{} where second{}(Y:S{}):=Y:S{} [] claim{} first{}(Z:S{}) []")).isSome = true := by decide +kernel

theorem heterogeneous_shadowing_checked :
    (checkText 32 (minimal "sort S{} [] sort T{} [] claim{} \\forall{S{}}(X:T{},\\exists{S{}}(X:S{},X:S{})) []")).isSome = true := by decide +kernel

theorem claims_only_checked :
    (checkText 32 (minimal "sort S{} [] claim{} \\bottom{S{}}() []")).isSome = true := by decide +kernel

theorem source_location_retained : base.source.location.tokenOffset = 2 ∧
    (base.localAxioms.get ⟨0, by decide +kernel⟩).location.tokenOffset = 4 := by decide +kernel

theorem rejects_forward_import :
    (checkText 32 "[] module A import B [] endmodule [] module B endmodule []").isNone = true := by decide +kernel

theorem rejects_late_import :
    (checkText 32 "[] module B endmodule [] module A sort S{} [] import B [] endmodule []").isNone = true := by decide +kernel

theorem rejects_duplicate_module :
    (checkText 32 "[] module A endmodule [] module A endmodule []").isNone = true := by decide +kernel

theorem rejects_global_name_collision :
    (checkText 32 (minimal "sort S{} [] symbol S{}():S{} []")).isNone = true := by decide +kernel

theorem rejects_missing_import_scope :
    (checkText 32 "[] module A sort S{} [] endmodule [] module B axiom{} \\top{S{}}() [] endmodule []").isNone = true := by decide +kernel

theorem rejects_wrong_arity :
    (checkText 32 (minimal "sort S{} [] symbol f{}(S{}):S{} [] claim{} f{}() []")).isNone = true := by decide +kernel

theorem rejects_sort_mismatch :
    (checkText 32 (minimal "sort S{} [] sort T{} [] claim{} \\and{S{}}(\\top{S{}}(),\\top{T{}}()) []")).isNone = true := by decide +kernel

theorem rejects_alias_extra_free_variable :
    (checkText 32 (minimal "sort S{} [] alias a{}(S{}):S{} where a{}(X:S{}):=Z:S{} []")).isNone = true := by decide +kernel

theorem rejects_alias_duplicate_parameters :
    (checkText 32 (minimal "sort S{} [] alias a{}(S{},S{}):S{} where a{}(X:S{},X:S{}):=X:S{} []")).isNone = true := by decide +kernel

theorem rejects_recursive_alias :
    (checkText 8 (minimal "sort S{} [] alias a{}(S{}):S{} where a{}(X:S{}):=a{}(X:S{}) []")).isNone = true := by decide +kernel

theorem rejects_conflicting_free_sorts :
    (checkText 32 (minimal "sort S{} [] sort T{} [] symbol f{}(S{},T{}):S{} [] claim{} f{}(X:S{},X:T{}) []")).isNone = true := by decide +kernel

theorem rejects_unknown_bound_sort :
    (checkText 32 (minimal "sort S{} [] claim{} \\exists{S{}}(X:T{},\\top{S{}}()) []")).isNone = true := by decide +kernel

theorem rejects_trailing_text : (checkText 32 (source ++ "module EXTRA")).isNone = true := by decide +kernel
end Silmaril.Logic.Kore.Modules.Examples
