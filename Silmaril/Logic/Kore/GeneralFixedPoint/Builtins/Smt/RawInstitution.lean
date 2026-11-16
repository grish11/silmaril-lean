module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Source
public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Institution

/-! The actual raw-source model boundary, using proved original raw adequacy. Each theory shares one finite named context, one source
builtin model, one raw set valuation and one actual source output value. -/
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open CategoryTheory Silmaril.Inst Silmaril.Logic.Smt
open Silmaril.Logic.Institution (Room Corridor)
variable [SortBindings]

structure SourcePoint (scope : Modules.Scope) (literalPrefix : String)
    (literals : List LiteralBinding) (hooks : List HookBinding)
    (names : List (ValueSort × String)) (s : ValueSort) where
  model : Model scope literalPrefix literals hooks
  objects : Semantics.Values model.native
  legal : ∀ binding ∈ names,
    (Semantics.lookupValue model.native objects binding.2 binding.1.name).isSome = true
  output : model.native.carrier s.name

structure RawSentence (scope : Modules.Scope) (hooks : List HookBinding)
    (names : List (ValueSort × String)) (s : ValueSort) where
  raw : RawPattern
  fuel : Nat
  pattern : Pattern s
  checked : check scope hooks fuel s raw = some pattern
  supportedNames : ∀ binding ∈ pattern.variables, binding ∈ names

def RawSentence.Satisfies {scope literalPrefix literals hooks names s}
    (p : RawSentence scope hooks names s)
    (point : SourcePoint scope literalPrefix literals hooks names s) : Prop :=
  point.output ∈ (Semantics.denote scope [] point.model.native point.model.carriers
    p.fuel [] point.objects s.name p.raw).getD ∅

def SourcePoint.standard {scope literalPrefix literals hooks names s}
    (point : SourcePoint scope literalPrefix literals hooks names s) : Point s :=
  ⟨sourceValuation point.model.carriers point.objects,
    sourceEquiv point.model.carriers s point.output⟩

theorem raw_characteristic_correct
    {scope literalPrefix literals hooks names s}
    (p : RawSentence scope hooks names s)
    (point : SourcePoint scope literalPrefix literals hooks names s) :
    Uflia.Quantified.Formula.Holds p.pattern.characteristic (target point.standard.1)
      (fun _ => point.standard.2) ↔ p.Satisfies point := by
  rw [characteristic_correct]
  have legal : LegalObjects point.objects p.pattern :=
    fun binding member => point.legal binding (p.supportedNames binding member)
  have raw := rawAdequacy scope hooks literalPrefix literals point.model point.objects
    p.fuel s p.raw p.pattern p.checked legal
  simp only [RawSentence.Satisfies, raw, Option.getD_some, Set.mem_ofPred_eq,
    SourcePoint.standard]

theorem raw_theory_models_iff
    {scope literalPrefix literals hooks names s}
    (H : Set (RawSentence scope hooks names s))
    (point : SourcePoint scope literalPrefix literals hooks names s) :
    (∀ p ∈ H, p.Satisfies point) ↔
      (∀ q ∈ (fun p : RawSentence scope hooks names s => p.pattern.characteristic) '' H,
        Uflia.Quantified.Formula.Holds q (target point.standard.1)
          (fun _ => point.standard.2)) := by
  constructor
  · intro h q hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact (raw_characteristic_correct p point).mpr (h p hp)
  · intro h p hp
    exact (raw_characteristic_correct p point).mp
      (h p.pattern.characteristic ⟨p, hp, rfl⟩)

theorem raw_theory_sat_iff
    {scope literalPrefix literals hooks names s}
    (H : Set (RawSentence scope hooks names s)) :
    (∃ point : SourcePoint scope literalPrefix literals hooks names s,
      ∀ p ∈ H, p.Satisfies point) ↔
    (∃ point : SourcePoint scope literalPrefix literals hooks names s,
      ∀ q ∈ (fun p : RawSentence scope hooks names s => p.pattern.characteristic) '' H,
        Uflia.Quantified.Formula.Holds q (target point.standard.1)
          (fun _ => point.standard.2)) :=
  exists_congr (raw_theory_models_iff H)

theorem raw_theory_unsat_iff
    {scope literalPrefix literals hooks names s}
    (H : Set (RawSentence scope hooks names s)) :
    (¬ ∃ point : SourcePoint scope literalPrefix literals hooks names s,
      ∀ p ∈ H, p.Satisfies point) ↔
    (¬ ∃ point : SourcePoint scope literalPrefix literals hooks names s,
      ∀ q ∈ (fun p : RawSentence scope hooks names s => p.pattern.characteristic) '' H,
        Uflia.Quantified.Formula.Holds q (target point.standard.1)
          (fun _ => point.standard.2)) :=
  not_congr (raw_theory_sat_iff H)

def rawSourceRoom (scope : Modules.Scope) (literalPrefix : String)
    (literals : List LiteralBinding) (hooks : List HookBinding)
    (names : List (ValueSort × String)) (s : ValueSort) : Room :=
  ⟨RawSentence scope hooks names s, Disc.cat (SourcePoint scope literalPrefix literals hooks names s),
    fun point p => p.Satisfies point⟩

def rawPairedTargetRoom (scope : Modules.Scope) (literalPrefix : String)
    (literals : List LiteralBinding) (hooks : List HookBinding)
    (names : List (ValueSort × String)) (s : ValueSort) : Room :=
  ⟨Characteristic s, Disc.cat (SourcePoint scope literalPrefix literals hooks names s),
    fun point p => Uflia.Quantified.Formula.Holds p (target point.standard.1)
      (fun _ => point.standard.2)⟩

def rawCorridor
    (scope : Modules.Scope) (literalPrefix : String)
    (literals : List LiteralBinding) (hooks : List HookBinding)
    (names : List (ValueSort × String)) (s : ValueSort) :
    Corridor (rawSourceRoom scope literalPrefix literals hooks names s)
      (rawPairedTargetRoom scope literalPrefix literals hooks names s) :=
  ⟨fun p => p.pattern.characteristic, 𝟭 _,
    fun point p => raw_characteristic_correct p point⟩

theorem raw_modelExpansive
    (scope : Modules.Scope) (literalPrefix : String)
    (literals : List LiteralBinding) (hooks : List HookBinding)
    (names : List (ValueSort × String)) (s : ValueSort) :
    (rawCorridor scope literalPrefix literals hooks names s).ModelExpansive :=
  fun point => ⟨point, rfl⟩

theorem raw_entails_iff
    (scope : Modules.Scope) (literalPrefix : String)
    (literals : List LiteralBinding) (hooks : List HookBinding)
    (names : List (ValueSort × String)) (s : ValueSort)
    (H : Set (RawSentence scope hooks names s)) (p : RawSentence scope hooks names s) :
    (rawSourceRoom scope literalPrefix literals hooks names s).Entails H p ↔
      (rawPairedTargetRoom scope literalPrefix literals hooks names s).Entails
        ((fun p : RawSentence scope hooks names s => p.pattern.characteristic) '' H)
        p.pattern.characteristic :=
  (rawCorridor scope literalPrefix literals hooks names s).entails_map_iff
    (raw_modelExpansive scope literalPrefix literals hooks names s) H p

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
