module

public import Silmaril.Compile.Category.Compiler.Defs
public import Silmaril.Courses.Cambridge.L1.LetIter.Thms

/-! # The L1 lowering in the behavioural compiler category

A behaviour records the input store and one complete outcome. A return
records the value and final store, a finite error records the stuck store,
and divergence means an infinite L1 trace or an undefined target computation.
The target programs
are independently typed closed LetIter terms over the L1 instructions.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L1.LetIter.Compilation

open Silmaril.Compile.Category
open Silmaril.Isotope.LetIter.ProofRelevant
open Silmaril.Semantics.Operational
open EffectfulDenotational (run)

structure SourceProgram where
  locations : TypeEnv
  result : L1.Ty
  expr : Expr
  typed : L1.HasType locations expr result

structure TargetProgram where
  locations : TypeEnv
  result : L1.Ty
  code : Lowered .nil (lowerTy result)

/-- Initial store and complete outcome. A `none` outcome denotes divergence. -/
abbrev Observation := Store × Option (Except Unit Expr × Store)

def sourceObserves (p : SourceProgram) : Observation → Prop
  | (s, some (.ok value, t)) =>
      OperationalInstitution.semantics.May ⟨p.expr, s⟩ (.returned ⟨value, t⟩)
  | (s, some (.error (), t)) =>
      ∃ out, Steps ⟨p.expr, s⟩ ⟨out, t⟩ ∧ Stuck ⟨out, t⟩
  | (s, none) => InfiniteTrace Step ⟨p.expr, s⟩

/-- Interpret the target term in the actual LetIter Kleisli model. -/
noncomputable def targetEvaluate (p : TargetProgram) : EffectfulDenotational.Computation Expr :=
  observe p.result ((Semantics.Categorical.denoteOfType
    (ε := Bool) (m := EffectfulDenotational.Computation) p.code.2).of (PUnit.unit, PUnit.unit))

def targetObserves (p : TargetProgram) : Observation → Prop
  | (s, some result) => result ∈ run (targetEvaluate p) s
  | (s, none) => ¬ (run (targetEvaluate p) s).Dom

def source : Language where
  Prog := SourceProgram
  Iface := TypeEnv × L1.Ty
  iface p := (p.locations, p.result)
  Obs := Observation
  beh p := {o | sourceObserves p o}

def target : Language where
  Prog := TargetProgram
  Iface := TypeEnv × TargetTy
  iface p := (p.locations, lowerTy p.result)
  Obs := Observation
  beh p := {o | targetObserves p o}

/-- The source and target share the store interface and decoded observations.
Only the type of the result changes at this boundary. -/
def convention : Convention source target where
  Φ := fun (locations, result) => (locations, lowerTy result)
  R := Eq

def translate (p : SourceProgram) : TargetProgram :=
  ⟨p.locations, p.result, lower p.expr p.result p.typed .nil⟩

/-- The generated target has exactly the source behaviours for every input
store, including finite errors and divergence. -/
theorem behaviours_eq (p : SourceProgram) : target.beh (translate p) = source.beh p := by
  ext observation
  change targetObserves (translate p) observation ↔ sourceObserves p observation
  obtain ⟨s, result⟩ := observation
  cases result with
  | none => exact diverges_iff p.typed s
  | some result =>
      obtain ⟨outcome, t⟩ := result
      cases outcome with
      | ok out => exact return_iff p.typed s ⟨out, t⟩
      | error error =>
          cases error
          exact error_iff p.typed s t

theorem translate_valid (p : SourceProgram) : Valid convention p (translate p) := by
  apply (valid_iff_beh convention p (translate p)).2
  exact ⟨rfl, fun o ho => ⟨o, behaviours_eq p ▸ ho, rfl⟩⟩

/-- Lowering succeeds on every program admitted by the source typing premise. -/
def compiler : Compiler source target where
  conv := convention
  run p := some (translate p)
  sound p _ h := (Option.some.inj h) ▸ translate_valid p

end Silmaril.Courses.Cambridge.L1.LetIter.Compilation
