module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics.Thms
public import Silmaril.Logic.Matching.GeneralFixedPoint.Institution
public import Silmaril.Logic.Institution.Borrowing

-- Configurable builtin names intentionally have a canonical fallback instance.
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
variable [sorts : SortBindings]
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)

/-- A named source pattern together with an actual successful elaboration.
Contexts remain explicit; no unchecked raw pattern is a source sentence. -/
structure CheckedSentence (scope : Modules.Scope) (literals : List LiteralBinding) (literalPrefix : String) where
  aliases : List Alias
  moduleIndex : Nat
  fuel : Nat
  sets : Names
  objects : Names
  sort : String
  raw : RawPattern
  typed : Pattern scope sets objects sort
  accepted : Checking.elaborate scope aliases literals literalPrefix moduleIndex fuel sets objects sort raw = some typed
  admitted : typed.admissible = true

def CheckedSentence.lower {scope : Modules.Scope} {literals : List LiteralBinding} {literalPrefix : String} (p : CheckedSentence scope literals literalPrefix) :
    Matching.GeneralFixedPoint.Sentence scope.signature :=
  ⟨p.sets.length, p.objects.length, context p.sets, context p.objects, p.sort, p.typed, p.admitted⟩

/-- Satisfaction runs the independent raw interpreter, universally quantifying
both object and set valuations. -/
def CheckedSentence.Satisfies {scope : Modules.Scope} {literals : List LiteralBinding} {literalPrefix : String} {hooks : List HookBinding}
    (M : Model scope literalPrefix literals hooks) (p : CheckedSentence scope literals literalPrefix) : Prop :=
  ∀ (v : ∀ i, M.native.carrier (context p.objects i))
    (η : ∀ i, Set (M.native.carrier (context p.sets i))) (x : M.native.carrier p.sort),
    x ∈ (Semantics.denote scope p.aliases M.native M.carriers p.fuel (Semantics.interpret M.native p.sets η)
      (Semantics.interpret M.native p.objects (fun i => {v i})) p.sort p.raw).getD ∅

theorem CheckedSentence.satisfies_lower {scope : Modules.Scope} {literals : List LiteralBinding} {literalPrefix : String} {hooks : List HookBinding}
    (M : Model scope literalPrefix literals hooks) (p : CheckedSentence scope literals literalPrefix) :
    p.Satisfies M ↔ Matching.GeneralFixedPoint.Sentence.Satisfies M.native p.lower := by
  change (∀ v η x, x ∈ (Semantics.denote scope p.aliases M.native M.carriers p.fuel _ _ p.sort p.raw).getD ∅) ↔ _
  simp only [Semantics.elaborate_sound p.aliases M.native literals literalPrefix hooks M.carriers M.laws p.fuel p.moduleIndex p.sets p.objects p.sort p.raw
    p.typed _ _ p.accepted, Option.getD_some]
  rfl

/-- A checked top pattern is globally valid, unlike a singleton Boolean
computation. This fact does not assume any carrier is a singleton. -/
theorem CheckedSentence.top_satisfies {scope : Modules.Scope} {literals : List LiteralBinding}
    {literalPrefix : String} {hooks : List HookBinding}
    (M : Model scope literalPrefix literals hooks) (p : CheckedSentence scope literals literalPrefix)
    (raw : p.raw = .top p.sort) : p.Satisfies M := by
  have accepted := p.accepted
  rw [raw] at accepted
  cases fuel : p.fuel with
  | zero => simp [fuel, Checking.elaborate] at accepted
  | succ n =>
    simp only [fuel, Checking.elaborate] at accepted
    split at accepted
    · rename_i valid
      intro v η x
      simp only [raw, fuel, Semantics.denote, valid, ↓reduceIte, Option.getD_some,
        Set.mem_univ]
    · contradiction

/-- Fixed-scope source room. Cross-signature builtin-carrier transport is not
part of this corridor. Both ends use all actual native homomorphisms between
models satisfying the declared literal and hook laws. -/
def sourceRoom (scope : Modules.Scope) (literals : List LiteralBinding) (literalPrefix : String) (hooks : List HookBinding) : Room :=
  ⟨CheckedSentence scope literals literalPrefix, Cat.of (Model scope literalPrefix literals hooks),
    CheckedSentence.Satisfies⟩

def loweringCorridor (scope : Modules.Scope) (literals : List LiteralBinding) (literalPrefix : String) (hooks : List HookBinding) :
    Corridor (sourceRoom scope literals literalPrefix hooks) (nativeRoom scope literalPrefix literals hooks) :=
  ⟨CheckedSentence.lower, 𝟭 _, fun M p => (p.satisfies_lower M).symm⟩

theorem lowering_modelExpansive (scope : Modules.Scope) (literals : List LiteralBinding) (literalPrefix : String)
    (hooks : List HookBinding) : (loweringCorridor scope literals literalPrefix hooks).ModelExpansive :=
  fun M => ⟨M, rfl⟩

theorem models_lower_iff {scope : Modules.Scope} {literals : List LiteralBinding} {literalPrefix : String} {hooks : List HookBinding}
    (H : Set (CheckedSentence scope literals literalPrefix)) (M : Model scope literalPrefix literals hooks) :
    (∀ p ∈ H, p.Satisfies M) ↔
      (∀ q ∈ CheckedSentence.lower '' H, Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) := by
  constructor
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact (p.satisfies_lower M).mp (h p hp)
  · intro h p hp
    exact (p.satisfies_lower M).mpr (h p.lower ⟨p, hp, rfl⟩)

theorem satisfiable_iff {scope : Modules.Scope} {literals : List LiteralBinding} {literalPrefix : String} (hooks : List HookBinding)
    (H : Set (CheckedSentence scope literals literalPrefix)) :
    (∃ M : Model scope literalPrefix literals hooks, ∀ p ∈ H, p.Satisfies M) ↔
      (∃ M : Model scope literalPrefix literals hooks, ∀ q ∈ CheckedSentence.lower '' H,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) :=
  exists_congr (models_lower_iff H)

theorem unsatisfiable_iff {scope : Modules.Scope} {literals : List LiteralBinding} {literalPrefix : String} (hooks : List HookBinding)
    (H : Set (CheckedSentence scope literals literalPrefix)) :
    (¬ ∃ M : Model scope literalPrefix literals hooks, ∀ p ∈ H, p.Satisfies M) ↔
      (¬ ∃ M : Model scope literalPrefix literals hooks, ∀ q ∈ CheckedSentence.lower '' H,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) :=
  not_congr (satisfiable_iff hooks H)

theorem entails_iff (scope : Modules.Scope) (literals : List LiteralBinding) (literalPrefix : String) (hooks : List HookBinding)
    (H : Set (CheckedSentence scope literals literalPrefix)) (p : CheckedSentence scope literals literalPrefix) :
    (sourceRoom scope literals literalPrefix hooks).Entails H p ↔
      (nativeRoom scope literalPrefix literals hooks).Entails (CheckedSentence.lower '' H) p.lower :=
  (loweringCorridor scope literals literalPrefix hooks).entails_map_iff
    (lowering_modelExpansive scope literals literalPrefix hooks) H p

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
