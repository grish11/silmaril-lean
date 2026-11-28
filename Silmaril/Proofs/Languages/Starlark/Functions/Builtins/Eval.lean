module

public import Silmaril.Languages.Starlark.Functions.Builtins.Operational.Defs
import Silmaril.Languages.Starlark.Lists.Iteration.Thms
import Silmaril.Languages.Starlark.Binary64.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Builtins

open Silmaril.Languages.Starlark.Binary64 (absolute_iff_abs)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Builtins
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration
  (Cursor acquireIterator cursorCollects_iff_collect finishState iterationSource map_finishState
    projectCell_finishState truth truth_finishState)

private theorem runBind {α β : Type} (first : Meaning α) (next : α → Meaning β)
    (state : State) : (first >>= next) state = Outcome.resume (first state) next := by
  cases h : first state <;> simp [bind, EStateM.bind, Outcome.resume, h]

private theorem runMap {α β : Type} (f : α → β) (first : Meaning α) (state : State) :
    (f <$> first) state = Outcome.resume (first state) (fun value => pure (f value)) := by
  cases h : first state <;> simp [Functor.map, EStateM.map, Outcome.resume, h] <;> rfl

private theorem items_eq_of_reads {id : Builtin} {state : State}
    {value : Value} {out : Outcome (List Value)} (h : Items id state value out) :
    items id value state = out := by
  cases h with
  | list address =>
    simp only [items, iterationSource, runMap]
    cases listElements address state <;> rfl
  | tuple address =>
    simp only [items, iterationSource, runMap]
    cases tupleElements address state <;> rfl
  | dict address =>
    simp only [items, iterationSource, runMap]
    cases dictEntries address state <;> rfl
  | range yields =>
    exact congrArg (fun values => EStateM.Result.ok values state) ((cursorCollects_iff_collect _ _).mp yields)
  | invalid h =>
    cases value <;> simp_all [IsCollection] <;> rfl

private theorem reads_items (id : Builtin) (state : State) (value : Value) :
    Items id state value (items id value state) := by
  cases value with
  | list address => exact items_eq_of_reads (.list address) ▸ Items.list address
  | tuple address => exact items_eq_of_reads (.tuple address) ▸ Items.tuple address
  | dict address => exact items_eq_of_reads (.dict address) ▸ Items.dict address
  | range => exact .range ((cursorCollects_iff_collect _ _).mpr rfl)
  | scalar | string | builtin | function => exact .invalid (by simp [IsCollection])

theorem truthCursor_eq_of_scans {stop : Bool} {cursor : Cursor} {state : State} {out : Outcome Value}
    (scan : TruthScans stop cursor state out) : truthCursor stop cursor state = out := by
  induction scan with
  | done step => rw [truthCursor, step]
  | decisive step tested =>
    rw [truthCursor, step]
    simp only [tested, Outcome.resume, ite_true]
  | next step tested _ ih =>
    have opposite : (!stop) ≠ stop := by cases stop <;> decide
    rw [truthCursor, step]
    simpa only [tested, Outcome.resume, ite_eq_right opposite] using ih
  | failed step tested =>
    rw [truthCursor, step]
    simp only [tested, Outcome.resume]

theorem scans_truthCursor (stop : Bool) (cursor : Cursor) (state : State) :
    TruthScans stop cursor state (truthCursor stop cursor state) := by
  rw [truthCursor]
  cases step : cursor.advance with
  | none => exact .done step
  | some item =>
    obtain ⟨value, rest⟩ := item
    dsimp only
    cases tested : truth value state with
    | error error next => exact .failed step tested
    | ok flag next =>
      simp only [Outcome.resume]
      by_cases decisive : flag = stop
      · rw [ite_eq_left decisive]
        exact .decisive step (decisive ▸ tested)
      · have opposite : flag = !stop := by cases flag <;> cases stop <;> simp_all
        rw [ite_eq_right decisive]
        exact .next step (opposite ▸ tested) (scans_truthCursor stop rest next)
termination_by cursor.remaining
decreasing_by exact Cursor.advance_decreases step

private theorem quantify_eq_of_quantifies {id : Builtin} {stop : Bool} {state : State}
    {value : Value} {out : Outcome Value} (ran : Quantifies id stop state value out) :
    quantify id stop value state = out := by
  cases ran with
  | scan acquired scan => simpa only [quantify, acquired] using truthCursor_eq_of_scans scan
  | nonIterable rejected => simp only [quantify, rejected, ite_true]
  | readError rejected other => simp only [quantify, rejected, ite_eq_right other]

private theorem quantifies_quantify (id : Builtin) (stop : Bool) (state : State) (value : Value) :
    Quantifies id stop state value (quantify id stop value state) := by
  rw [quantify]
  cases acquired : acquireIterator value state with
  | ok iterator next =>
    obtain ⟨guard, cursor⟩ := iterator
    exact .scan acquired (scans_truthCursor stop cursor next)
  | error error next =>
    dsimp only
    by_cases unsupported : error = .notIterable
    · rw [ite_eq_left unsupported]
      exact .nonIterable (unsupported ▸ acquired)
    · rw [ite_eq_right unsupported]
      exact .readError acquired unsupported

private theorem scans_finishState {stop : Bool} {cursor : Cursor} {state : State} {out : Outcome Value}
    (scan : TruthScans stop cursor state out) : finishState out = state := by
  induction scan with
  | done => rfl
  | @decisive _ _ value s _ _ tested | @failed _ _ value s _ _ _ tested =>
    simpa only [tested, finishState] using truth_finishState value s
  | @next _ _ value s _ _ _ tested _ ih =>
    exact ih.trans (by simpa only [tested, finishState] using truth_finishState value s)

theorem quantify_finishState (id : Builtin) (stop : Bool) (state : State) (value : Value) :
    finishState (quantify id stop value state) = state := by
  have unchanged : finishState (acquireIterator value state) = state := by
    cases value <;> simp [acquireIterator, iterationSource, map_finishState, listElements,
      tupleElements, dictEntries, projectCell_finishState] <;> rfl
  rw [quantify]
  cases acquired : acquireIterator value state with
  | error => simpa only [acquired, finishState] using unchanged
  | ok iterator next =>
    obtain ⟨_, cursor⟩ := iterator
    exact (scans_finishState (scans_truthCursor stop cursor next)).trans
      (by simpa only [acquired, finishState] using unchanged)

theorem invoke_eq_of_invokes {state : State} {id : Builtin} {args : Actual} {out : Outcome Value}
    (h : Invokes state id args out) : invoke id args state = out := by
  cases h with
  | missing h => cases id <;> simp_all [minArity] <;> rfl
  | extra excluded => cases id <;> simp_all [invoke] <;> rfl
  | bool => exact runMap _ _ _
  | @lenCollection value out noString noRange reads =>
    have read := items_eq_of_reads reads
    cases value with
    | string => exact (noString _ rfl).elim
    | range => exact (noRange _ rfl).elim
    | _ => exact (runMap (countValue ∘ List.length) _ state).trans (by rw [read]; rfl)
  | list reads => exact (runBind _ allocate state).trans (by rw [items_eq_of_reads reads])
  | tuple reads => exact (runBind _ allocateTuple state).trans (by rw [items_eq_of_reads reads])
  | @absFloat input output magnitude =>
    rw [← (absolute_iff_abs input output).mp magnitude]
    rfl
  | @absType value noInt noFloat =>
    cases value with
    | scalar value => cases value <;> simp_all <;> rfl
    | _ => rfl
  | any ran | all ran => exact quantify_eq_of_quantifies ran
  | _ => rfl

theorem invokes_invoke (state : State) (id : Builtin) (args : Actual) :
    Invokes state id args (invoke id args state) := by
  obtain ⟨positional, keywords⟩ := args
  cases keywords with
  | cons entry rest => cases entry; exact .keyword
  | nil =>
    cases positional with
    | nil =>
      cases id with
      | bool => exact .emptyBool
      | list => exact .emptyList
      | tuple => exact .emptyTuple
      | _ => exact .missing rfl
    | cons value tail =>
      cases tail with
      | cons second rest =>
        cases id with
        | range =>
          rcases rest with _ | ⟨_, _ | ⟨_, _⟩⟩
          · exact .rangeTwo
          · exact .rangeThree
          · exact .rangeExtra
        | _ => exact .extra (by decide)
      | nil =>
        cases id with
        | bool =>
          change Invokes state .bool ⟨[value], []⟩ ((boolValue <$> truth value) state)
          rw [runMap]
          exact .bool
        | type => exact .type
        | list =>
          change Invokes state .list ⟨[value], []⟩ ((items .list value >>= allocate) state)
          rw [runBind]
          exact .list (reads_items .list state value)
        | tuple =>
          change Invokes state .tuple ⟨[value], []⟩ ((items .tuple value >>= allocateTuple) state)
          rw [runBind]
          exact .tuple (reads_items .tuple state value)
        | range => exact .rangeOne
        | any => exact .any (quantifies_quantify .any true state value)
        | all => exact .all (quantifies_quantify .all false state value)
        | abs =>
          cases value with
          | scalar value =>
            cases value with
            | int => exact .absInt
            | float x => exact .absFloat ((absolute_iff_abs x _).mpr rfl)
            | _ => exact .absType (by intro _ equality; cases equality) (by intro _ equality; cases equality)
          | _ => exact .absType (by intro _ equality; cases equality) (by intro _ equality; cases equality)
        | len =>
          cases value with
          | string => exact .lenString
          | range => exact .lenRange
          | scalar | list | tuple | dict | function | builtin =>
            change Invokes state .len ⟨[_], []⟩ (((countValue ∘ List.length) <$> items .len _) state)
            rw [runMap]
            exact .lenCollection (by intro _ equality; cases equality)
              (by intro _ equality; cases equality) (reads_items .len state _)

end Silmaril.Proofs.Languages.Starlark.Functions.Builtins
