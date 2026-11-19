module

public import Silmaril.Cerberus.Elaboration.State.Defs
public import Silmaril.Cerberus.Ail.Defs

/-! Pinned `translation.lem:3300–3459` at Cerberus
`b3e11ea334e95359907d4abf9194f0e7fedc6c6a`: loop-control erasure and label
visibility collection. These operations transform typed Ail, not source text.
They neither construct a replacement function body nor discharge a refinement.
Freshness exhaustion and invalid break/continue targets reject explicitly. -/

@[expose] public section
namespace Silmaril.Cerberus.Elaboration.LoopControl
open Silmaril.Cerberus

structure Targets where
  continueLabel : Option Sym := none
  breakLabel : Option Sym := none

def freshLabel (labelPrefix : String) : State.ElabM Sym := do
  let context ← get
  match Freshness.prettyWithId (fun index => labelPrefix ++ toString index) context.freshness with
  | .error error => throw (.freshness error)
  | .ok (symbol, after) =>
      set {context with freshness := after}
      return symbol

/-- New statements have the upstream `mk_statement` empty provenance/attributes.
The enclosing original statement retains all its original wrappers. -/
def generated {α : Type} (location : Loc) (node : Ail.StatementNode α) : Ail.Statement α :=
  .mk location ⟨false, none⟩ ⟨[]⟩ node

/-- Allocate continue before break, then restore outer targets by lexical scope.
Switch uses its own target pair just as the pinned source does. -/
def erase (statement : Ail.TypedStatement) (targets : Targets := {}) :
    State.ElabM Ail.TypedStatement := do
  let .mk location provenance attributes node := statement
  let output : Ail.StatementNode Ail.GenTypeCategory ← match _hnode : node with
    | .block bindings statements => do
        pure <| .block bindings (← statements.attach.mapM fun child => erase child.val targets)
    | .if_ condition yes no => do
        pure <| .if_ condition (← erase yes targets) (← erase no targets)
    | .while_ condition body loopId => do
        let continueLabel ← freshLabel "continue_"
        let breakLabel ← freshLabel "break_"
        let body ← erase body ⟨some continueLabel, some breakLabel⟩
        pure <| .block [] [generated location (.while_ condition
          (generated location (.block [] [body,
            generated location (.label continueLabel (generated location .skip)
              (some (.loopContinue loopId)))])) loopId),
          generated location (.label breakLabel (generated location .skip)
            (some (.loopBreak loopId)))]
    | .do_ body condition loopId => do
        let continueLabel ← freshLabel "continue_"
        let breakLabel ← freshLabel "break_"
        let body ← erase body ⟨some continueLabel, some breakLabel⟩
        pure <| .block [] [generated location (.do_
          (generated location (.block [] [body,
            generated location (.label continueLabel (generated location .skip)
              (some (.loopContinue loopId)))])) condition loopId),
          generated location (.label breakLabel (generated location .skip)
            (some (.loopBreak loopId)))]
    | .break_ => do
        let some label := targets.breakLabel | throw (.message "break has no enclosing target")
        pure <| .goto label
    | .continue_ => do
        let some label := targets.continueLabel | throw (.message "continue has no enclosing target")
        pure <| .goto label
    | .switch condition body => do
        let continueLabel ← freshLabel "continue_"
        let breakLabel ← freshLabel "break_"
        let body ← erase body ⟨some continueLabel, some breakLabel⟩
        pure <| .block [] [generated location (.switch condition
          (generated location (.block [] [generated location (.goto breakLabel), body]))),
          generated location (.label breakLabel (generated location .skip) (some .switch))]
    | .case_ value body => do pure <| .case_ value (← erase body targets)
    | .caseRangeGnu first last body => do pure <| .caseRangeGnu first last (← erase body targets)
    | .default body => do pure <| .default (← erase body targets)
    | .label label body annotation => do pure <| .label label (← erase body targets) annotation
    | .par statements => do pure <| .par (← statements.attach.mapM fun child => erase child.val targets)
    | .marker id body => do pure <| .marker id (← erase body targets)
    | other => do pure other
  return .mk location provenance attributes output
termination_by sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have memberBound := List.sizeOf_lt_of_mem child.property
      omega

abbrev Visible := Sym × Ctype
abbrev Labels := List (Sym × List Visible)

/-- Collect lexical object types at each actual/generated label. Block bindings
are prepended in source order; leaving a block restores the enclosing scope.
Function-argument objects, when used, are appended separately by the caller. -/
def collect (statement : Ail.TypedStatement) (visible : List Visible := []) : Labels :=
  let .mk _ _ _ node := statement
  match node with
  | .block bindings statements =>
      let localObjects := bindings.map fun (symbol, (_, _, _, type)) => (symbol, type)
      statements.attach.flatMap fun child => collect child.val (localObjects ++ visible)
  | .if_ _ yes no => collect yes visible ++ collect no visible
  | .while_ _ body _ | .do_ body _ _ | .switch _ body |
      .case_ _ body | .caseRangeGnu _ _ body | .default body | .marker _ body =>
      collect body visible
  | .label label body _ => (label, visible) :: collect body visible
  | .par statements => statements.attach.flatMap fun child => collect child.val visible
  | _ => []
termination_by sizeOf statement
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have memberBound := List.sizeOf_lt_of_mem child.property
      omega

/-- Match source Map.insert semantics, including last insertion for the same
semantic symbol key. Printed descriptions do not determine label identity. -/
def lookup (labels : Labels) (label : Sym) : Option (List Visible) :=
  (labels.reverse.find? (fun entry => decide (entry.1.key = label.key))).map Prod.snd

attribute [cbv_eval] erase.eq_def collect.eq_def

end Silmaril.Cerberus.Elaboration.LoopControl
