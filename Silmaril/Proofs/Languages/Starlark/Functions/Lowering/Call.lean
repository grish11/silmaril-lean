module

public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Atoms
public import Silmaril.Languages.Starlark.Functions.Expressions.Thms
public import Silmaril.Languages.Starlark.Functions.Builtins.Thms
public import Silmaril.Languages.Starlark.Lists.Iteration.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Iteration
  (Cursor Flow acquireIterator finishState map_finishState projectCell_finishState truth)

private theorem packAction (signature : Signature) (bound : BoundArguments) :
    FrameAction (packArgs signature bound) := by
  cases varargs : signature.varargs <;> cases kwargs : signature.kwargs <;>
    simp only [packArgs, varargs, kwargs, pure_bind]
  · exact actionPure _
  · exact actionBind (actionAllocateDict _) fun _ => actionPure _
  · exact actionBind (actionAllocateTuple _) fun _ => actionPure _
  · exact actionBind (actionAllocateTuple _) fun _ =>
      actionBind (actionAllocateDict _) fun _ => actionPure _

private theorem truthCursorFrame (stop : Bool) (cursor : Cursor) :
    FrameIndependent (Builtins.truthCursor stop cursor) := by
  intro state bindings
  conv =>
    lhs
    rw [Builtins.truthCursor]
  conv =>
    rhs
    rw [Builtins.truthCursor]
  cases step : cursor.advance with
  | none => rfl
  | some item =>
    obtain ⟨value, rest⟩ := item
    dsimp only
    rw [frameTruth value state bindings]
    cases tested : truth value state with
    | error => rfl
    | ok flag next =>
      simp only [mapFrame, Outcome.resume]
      by_cases decisive : flag = stop
      · simp only [ite_eq_left decisive]
      · simp only [ite_eq_right decisive]
        exact truthCursorFrame stop rest next bindings
termination_by cursor.remaining
decreasing_by exact Cursor.advance_decreases step

private theorem quantifyAction (id : Builtin) (stop : Bool) (value : Value) :
    FrameAction (Builtins.quantify id stop value) := by
  constructor
  · intro state bindings
    simp only [Builtins.quantify, (acquireAction value).1 state bindings]
    cases acquireIterator value state with
    | error => rfl
    | ok iterator next =>
      obtain ⟨_, cursor⟩ := iterator
      exact truthCursorFrame stop cursor next bindings
  · intro state
    rw [Builtins.quantify_finishState]
    exact ⟨rfl, rfl⟩

private theorem builtinAction (id : Builtin) (actual : Actual) :
    FrameAction (Builtins.invoke id actual) := by
  have truthAction (value : Value) : FrameAction (Iteration.truth value) := by
    cases value with
    | list => exact actionMap _ (actionList _)
    | tuple => exact actionMap _ (actionTuple _)
    | dict => exact actionMap _ (actionDict _)
    | _ => exact actionPure _
  have itemsAction (id : Builtin) (value : Value) : FrameAction (Builtins.items id value) := by
    cases value with
    | list => exact actionMap Prod.snd (actionMap _ (actionList _))
    | tuple => exact actionMap Prod.snd (actionMap _ (actionTuple _))
    | dict => exact actionMap Prod.snd (actionMap _ (actionDict _))
    | range => exact actionPure _
    | _ => exact actionThrow _
  obtain ⟨positional, keywords⟩ := actual
  unfold Builtins.invoke
  cases keywords with
  | cons entry rest => cases entry; exact actionThrow _
  | nil =>
    cases positional with
    | nil =>
      cases id with
      | bool => exact actionPure _
      | list => exact actionAllocate _
      | tuple => exact actionAllocateTuple _
      | _ => exact actionThrow _
    | cons value rest =>
      cases rest with
      | cons =>
        cases id <;> first | exact actionThrow _ | exact actionExcept _
      | nil =>
        cases id with
        | bool => exact actionMap _ (truthAction value)
        | len =>
          cases value <;> first | exact actionPure _ | exact actionMap _ (itemsAction _ _)
        | type => exact actionPure _
        | list => exact actionBind (itemsAction _ _) actionAllocate
        | tuple => exact actionBind (itemsAction _ _) actionAllocateTuple
        | range => exact actionExcept _
        | abs =>
          cases value with
          | scalar v => cases v <;> first | exact actionPure _ | exact actionThrow _
          | _ => exact actionThrow _
        | any | all => exact quantifyAction _ _ _

private def transportPlan (bindings : Binding → Option Value) {available : List DeclarationId} :
    Outcome (CallPlan available) → Outcome (CallPlan available)
  | .ok (.closure plan) s => .ok (.closure plan) s
  | .ok (.builtin id actual) s => .ok (.builtin id actual) (rebind s bindings)
  | .error error s => .error error (rebind s bindings)

private theorem starFrame (star : Option Value) : FrameAction (expandStar star) := by
  cases star with
  | none => exact actionPure _
  | some value =>
    cases value with
    | list => exact actionList _
    | tuple => exact actionTuple _
    | dict => exact actionMap _ (actionDict _)
    | range => exact actionPure _
    | _ => exact actionThrow _

private theorem starStarFrame (starStar : Option Value) : FrameAction (expandStarStar starStar) := by
  cases starStar with
  | none => exact actionPure _
  | some value =>
    cases value with
    | dict => exact actionBind (actionDict _) fun _ => actionExcept _
    | _ => exact actionThrow _

private theorem expand_frame (args : EvaluatedArguments) : FrameIndependent args.expand :=
  frameBind (starStarFrame _).1 fun keys =>
    frameBind (starFrame _).1 fun values => framePure (Actual.mk (args.positional ++ values) (args.keywords ++ keys))

private theorem star_state (star : Option Value) (s : State) :
    finishState (expandStar star s) = s := by
  cases star with
  | none => rfl
  | some value =>
    cases value with
    | list | tuple => rw [expandStar]; exact projectCell_finishState _ _ s
    | dict => rw [expandStar, map_finishState]; exact projectCell_finishState _ _ s
    | _ => rfl

private theorem starStar_state (starStar : Option Value) (s : State) :
    finishState (expandStarStar starStar s) = s := by
  cases starStar with
  | none => rfl
  | some value =>
    cases value with
    | dict address =>
      simp only [expandStarStar, bind, EStateM.bind]
      have same : finishState (dictEntries address s) = s := projectCell_finishState _ _ s
      cases h : dictEntries address s with
      | error error next =>
        rw [h] at same
        change finishState (.error error next : Outcome (List Entry)) = s at same
        change next = s at same
        exact same
      | ok entries next =>
        rw [h] at same
        change next = s at same
        subst next
        have kept (out : Except Error (List (String × Value))) :
            finishState (fromExcept out s) = s := by cases out <;> rfl
        exact kept _
    | _ => rfl

private theorem expands_state {s : State} {args : EvaluatedArguments} {out : Outcome Actual}
    (h : Expands args s out) : finishState out = s := by
  cases h with
  | mappingError failed =>
    have same := starStar_state args.starStar s
    rw [failed] at same
    exact same
  | @spreadError keys next final error read failed =>
    have first := starStar_state args.starStar s
    have last := star_state args.star next
    rw [read] at first
    rw [(expandsStar_iff_expandStar _ _ _).mp failed] at last
    exact last.trans first
  | @success keys values next final read succeeded =>
    have first := starStar_state args.starStar s
    have last := star_state args.star next
    rw [read] at first
    rw [(expandsStar_iff_expandStar _ _ _).mp succeeded] at last
    exact last.trans first

private theorem prepare_frame (program : Program) (available : List DeclarationId)
    (actual : Actual) (callee : Value) (s : State) (f : Binding → Option Value) :
    prepareExpanded program available actual callee (rebind s f) =
      transportPlan f (prepareExpanded program available actual callee s) := by
  cases callee with
  | function address =>
    simp only [prepareExpanded, bind, EStateM.bind]
    have get := frameProject address (fun | .function c => some c | _ => none) s f
    change getClosure address (rebind s f) = mapFrame (rebind · f) (getClosure address s) at get
    rw [get]
    cases getClosure address s with
    | error => rfl
    | ok closure u =>
      dsimp only [mapFrame]
      cases program[closure.declaration]? with
      | none => rfl
      | some declaration =>
        by_cases permitted : closure.declaration ∈ available
        · simp only [dite_eq_left permitted, EStateM.bind]
          let bound := bindArguments declaration.signature closure.defaults actual
          have kept := frameFromExcept bound u f
          change fromExcept bound (rebind u f) = _ at kept
          rw [kept]
          cases fromExcept bound u with
          | error => rfl
          | ok assigned v =>
            simp only [mapFrame]
            rw [(packAction declaration.signature assigned).1 v f]
            cases packArgs declaration.signature assigned v <;> rfl
        · simp only [dite_eq_right permitted]
          rfl
  | _ => rfl

private theorem prepare_scope (program : Program) (available : List DeclarationId)
    (actual : Actual) (callee : Value) (s : State) :
    match prepareExpanded program available actual callee s with
    | .ok (.closure _) _ => True
    | .ok (.builtin _ _) t | .error _ t => SameScope t s := by
  cases callee with
  | function address =>
    simp only [prepareExpanded, bind, EStateM.bind]
    have kept := scopeProject address (fun | .function c => some c | _ => none) s
    change SameScope (finishState (getClosure address s)) s at kept
    cases he : getClosure address s with
    | error error next =>
      simpa only [he, finishState] using kept
    | ok closure next =>
      rw [he] at kept
      dsimp only
      cases entry : program[closure.declaration]? with
      | none => exact kept
      | some declaration =>
        by_cases permitted : closure.declaration ∈ available
        · simp only [dite_eq_left permitted]
          simp only [EStateM.bind]
          cases boundResult : bindArguments declaration.signature closure.defaults actual with
          | error => exact kept
          | ok bound =>
            simp only [fromExcept, pure, EStateM.pure]
            have packed := (packAction declaration.signature bound).2 next
            cases hp : packArgs declaration.signature bound next with
            | error err final =>
              rw [hp] at packed
              exact ⟨packed.1.trans kept.1, packed.2.trans kept.2⟩
            | ok => trivial
        · simp only [dite_eq_right permitted]
          exact kept
  | _ => exact ⟨rfl, rfl⟩

private theorem dispatch_scope {program : Program} {available : List DeclarationId}
    {s : State} {actual : Actual} {callee : Value} {out : Outcome Value}
    (h : Dispatches program available s callee actual out) : SameScope (finishState out) s := by
  have kept := prepare_scope program available actual callee s
  cases h with
  | reject rejected => simpa only [rejected, finishState] using kept
  | @builtin id bound next out prepared invoked =>
    rw [prepared] at kept
    have evaluated := (Builtins.invokes_iff_invoke _ _ _ _).mp invoked
    have run := (builtinAction id bound).2 next
    rw [evaluated] at run
    exact ⟨run.1.trans kept.1, run.2.trans kept.2⟩
  | returned | failed => exact ⟨rfl, rfl⟩

theorem applies_scope {program : Program} {available : List DeclarationId} {shape : ArgumentShape}
    {s : State} {values : List Value} {out : Outcome Value}
    (h : Applies program available shape s values out) : SameScope (finishState out) s := by
  cases h with
  | @expansionError callee operands error next failed =>
    have same := expands_state failed
    change next = s at same
    subst next
    exact ⟨rfl, rfl⟩
  | expanded expanded dispatched =>
    have same := expands_state expanded
    change _ = s at same
    exact same ▸ dispatch_scope dispatched

@[expose] def commit (target : Binding) : Outcome Value → Outcome Flow
  | .ok value s => .ok .next (s.write target value)
  | .error error s => .error error s

private theorem dispatch_lower {program : Program} {available : List DeclarationId}
    {s t : State} {callee : Value} {actual : Actual} {out : Outcome Value}
    (h : Dispatches program available s callee actual out)
    (same : StateMatch 0 s t) (target : Binding) :
    (match prepareExpanded program available actual callee t with
    | .error error next => .error error next
    | .ok (.closure plan) next =>
      completeCall t (some target) (denoteBody program (withoutDeclaration available plan.id) plan.body next)
    | .ok (.builtin id actual) next =>
      Outcome.resume (Builtins.invoke id actual next) (writeCallResult (some target))) =
      commit target (mapFrame (rebind · t.bindings) out) := by
  have prep := prepare_frame program available actual callee s t.bindings
  rw [same_rebound same] at prep
  rw [prep]
  cases h with
  | reject rejected => simp only [rejected, transportPlan, mapFrame, commit]
  | builtin prepared invoked =>
    rw [prepared]
    simp only [transportPlan]
    have executed := (Builtins.invokes_iff_invoke _ _ _ _).mp invoked
    rw [(builtinAction _ _).1, executed]
    cases out <;> rfl
  | @returned plan next final flow prepared ran =>
    rw [prepared]
    simp only [transportPlan, (exec_iff_denoteBody _ _ _ _ _).mp ran]
    cases flow <;>
      simp [completeCall, writeCallResult, commit, mapFrame, rebind, restoreCaller, ← same.slots, callValue]
  | failed prepared ran =>
    rw [prepared]
    simp only [transportPlan, (exec_iff_denoteBody _ _ _ _ _).mp ran]
    simp [completeCall, commit, mapFrame, rebind, restoreCaller, ← same.slots]

theorem lower_call {program : Program} {available : List DeclarationId} {shape : ArgumentShape}
    {s t : State} {values : List Value} {out : Outcome Value}
    (h : Applies program available shape s values out)
    (same : StateMatch 0 s t) (target : Binding)
    (callee : Languages.Starlark.Lists.Expr) (args : Arguments) (shapeEq : args.shape = shape)
    (readArgs : denote (Arguments.operands callee args) t = .ok values t) :
    denoteBody program available (.call (some target) callee args) t =
      commit target (mapFrame (rebind · t.bindings) out) := by
  rw [denoteBody, readArgs, Outcome.resume]
  cases h with
  | @expansionError callable operands error next failed =>
    have transported := frameRun (expand_frame (shape.collect operands)) same
    rw [expands_eq failed] at transported
    simp only [prepare, bind, EStateM.bind, Arguments.expand, shapeEq, transported, mapFrame, commit]
  | @expanded callable operands actual next out expanded dispatched =>
    have stopped := expands_state expanded
    change next = s at stopped
    subst next
    have transported := frameRun (expand_frame (shape.collect operands)) same
    rw [expands_eq expanded, mapFrame, same_rebound same] at transported
    simp only [prepare, bind, EStateM.bind, Arguments.expand, shapeEq, transported]
    exact dispatch_lower dispatched same target

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering
