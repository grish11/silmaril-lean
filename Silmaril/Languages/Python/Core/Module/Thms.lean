module

public import Silmaril.Languages.Python.Core.Module.Defs
import Silmaril.Proofs.Languages.Python.Core.Module.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Module

theorem scalarDictionaryGet_nil (key fallback : Value) :
    scalarDictionaryGet [] key fallback = fallback := rfl

theorem scalarDictionaryGet_snoc (entries : List (Value × Value)) (latestKey latestValue key fallback : Value) :
    scalarDictionaryGet (entries ++ [(latestKey, latestValue)]) key fallback =
      if latestKey.equal key then latestValue else scalarDictionaryGet entries key fallback := by
  cases matched : latestKey.equal key <;> simp [scalarDictionaryGet, dictionaryGet, List.reverse_append, matched]

theorem Identity.scan_iff {ε : Type} (left : Singleton)
    (links : List (IdentityOperator × (Unit → Except ε Singleton))) (result : Except ε Bool) :
    Identity.scan left links = result ↔ Identity.Scans left links result :=
  Proofs.Languages.Python.Core.Module.identity_scan_iff left links result

open Semantics.Operational

theorem Globals.lookup_bind (globals : Globals) (name : GlobalName) (value : Value) :
    (globals.bind name value).lookup name = some value := by simp [Globals.bind]

theorem Globals.lookup_bind_other (globals : Globals) {name query : GlobalName}
    (value : Value) (different : query ≠ name) :
    (globals.bind name value).lookup query = globals.lookup query := by simp [Globals.bind, different]

theorem Expr.eval_iff {expression : Expr} {globals : Globals} {result : Evaluated} :
    expression.eval globals = result ↔ expression.Evals globals result :=
  Proofs.Languages.Python.Core.Module.eval_iff

theorem State.advance_iff {source target : State} {label : Option Label} :
    source.advance = some (label, target) ↔ Step source label target :=
  Proofs.Languages.Python.Core.Module.advance_iff

theorem Step.deterministic {source left right : State} {a b : Option Label}
    (first : Step source a left) (second : Step source b right) : (a, left) = (b, right) :=
  Option.some.inj ((State.advance_iff.mpr first).symm.trans (State.advance_iff.mpr second))

theorem Step.decreases {source target : State} {label : Option Label}
    (step : Step source label target) : target.budget < source.budget :=
  Proofs.Languages.Python.Core.Module.step_decreases step

theorem Entry.start_iff {entry : Entry} {state : State} : model.initial entry state ↔ state = entry.start := Iff.rfl

theorem model_safe (entry : Entry) : ¬ model.UBReachable entry :=
  fun ⟨_, _, _, _, impossible⟩ => impossible

theorem noDiverges (source : State) : ¬ semantics.toOpSem.Diverges source :=
  Proofs.Languages.Python.Core.Module.noDiverges source

theorem run_path (fuel : Nat) (source : State) :
    labelled.Path source (runPrefix fuel source).1 (runPrefix fuel source).2 :=
  Proofs.Languages.Python.Core.Module.run_path fuel source

theorem Entry.run_finishes (entry : Entry) : ∃ observation, entry.run.2 = .finished observation :=
  Proofs.Languages.Python.Core.Module.run_finishes entry.start _ (Nat.le_refl _)

/-- The complete visible trace and observation, including the residual globals,
are exactly those computed by the entry runner. -/
theorem Entry.finishes_iff {entry : Entry} {log : List Label} {outcome : Outcome Observation} :
    labelled.Finishes entry.start log outcome ↔
      ∃ observation, entry.run = (log, .finished observation) ∧ outcome = .returned observation :=
  Proofs.Languages.Python.Core.Module.finishes_iff

end Silmaril.Languages.Python.Core.Module
