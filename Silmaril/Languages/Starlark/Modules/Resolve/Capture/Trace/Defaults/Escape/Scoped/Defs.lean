module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open Functions
open Assignment (LexicalBlock)
open Lists (State Outcome)

/-- The escaping wrapper can bind additional required positional parameters.
The whole lexical block includes assignments on either side of child installation. -/
structure Spec where
  wrapper : Escape.Spec
  assignments : List (String × Lowering.Resolve.SourceExpr)
  additional : List String := []
  updates : List (String × Int) := []
  leading : List (String × Lowering.Resolve.SourceExpr) := []

@[expose] def Spec.child (spec : Spec) : Defaults.Body.Definition :=
  ⟨spec.wrapper.childName, spec.wrapper.child.parameters,
    spec.assignments.foldr (fun (name, rhs) rest => .assign name rhs rest)
      (.ret (.scalar (.read spec.wrapper.returned)))⟩

@[expose] def Spec.parameters (spec : Spec) : List String := spec.wrapper.parameter :: spec.additional

@[expose] def Spec.enclosing (spec : Spec) : List String := spec.parameters ++ spec.wrapper.locals spec.updates spec.additional (spec.leading.map Prod.fst)

@[expose] def Spec.frame (spec : Spec) (childId : Nat) : Forwarding.Frame :=
  spec.wrapper.frame childId spec.additional spec.updates (spec.leading.map Prod.fst)

@[expose] def Spec.command (spec : Spec) : Command :=
  spec.wrapper.commandWith spec.child.body.source spec.additional spec.updates spec.leading

@[expose] def Spec.block (spec : Spec) (globals : List String) : LexicalBlock :=
  ⟨spec.enclosing, [], globals⟩

structure Names (spec : Spec) : Prop where
  wrapper : Escape.WrapperNames spec.wrapper
  childFresh : spec.wrapper.childName ∉ spec.additional
  localUpdates : ∀ name ∈ spec.updates.map Prod.fst, name ∉ spec.parameters ∧ name ≠ spec.wrapper.childName

/-- The independent body relation determines the entire capture order.
The wrapper profile permits parameter and wrapper-local captures. -/
structure Plan (globals : List String) (spec : Spec) where
  body : Defaults.Body.Plan globals spec.child spec.enclosing
  captured : ∀ entry ∈ body.free, ∃ name ∈ spec.enclosing,
    name ≠ spec.wrapper.childName ∧ entry = ⟨fileSlot name, fileSlot name⟩
  leadingCode : List (String × Lowering.Expr)
  leadingReads : List Binding
  leading : Defaults.Body.ElaboratesPrefix (spec.block globals) spec.leading leadingCode leadingReads
  defaultItems : List PlainPositionalDefault
  defaults : Lexical.Elaborates (spec.block globals) spec.child.parameters.optional defaultItems
  moduleFree : List FreeName
  selects : Selects (spec.block globals) (leadingReads ++ defaultItems.flatMap PlainPositionalDefault.reads) moduleFree

@[expose] def Plan.defaultCodes {globals : List String} {spec : Spec} (plan : Plan globals spec) : List Lowering.Expr :=
  plan.defaultItems.map PlainPositionalDefault.value

@[expose] def Plan.childDeclaration {globals : List String} {spec : Spec} (plan : Plan globals spec) : Declaration :=
  plan.body.declaration plan.defaultCodes

@[expose] def Plan.frame {globals : List String} {spec : Spec} (plan : Plan globals spec) (id : Nat) :
    Forwarding.Frame :=
  let frame := spec.frame id
  { frame with free := plan.moduleFree, code := Defaults.Body.prependCode plan.leadingCode frame.code }

/-- Prefix failure restores the caller before defaults or installation.
Success supplies exactly the reached wrapper state to the existing rules. -/
inductive Returns {globals : List String} {spec : Spec} (plan : Plan globals spec)
    (childId : Nat) (caller : State) (captures : List Lists.Capture)
    (assigned : List (Binding × Lists.Value)) : Outcome Lists.Value → Prop where
  | failed {error : Lists.Error} {final : State} :
      Defaults.Body.RunsPrefix (spec.block globals) (activate caller (plan.frame childId).declaration captures assigned)
        spec.leading plan.leadingCode (.error error final) →
      Returns plan childId caller captures assigned (.error error (restoreCaller caller final))
  | entered {reached : State} {out : Outcome Lists.Value} :
      Defaults.Body.RunsPrefix (spec.block globals) (activate caller (plan.frame childId).declaration captures assigned)
        spec.leading plan.leadingCode (.ok () reached) →
      Escape.ReturnsWith spec.wrapper (spec.block globals) plan.defaultItems childId plan.body.free spec.updates caller reached out →
      Returns plan childId caller captures assigned out

structure Admitted (globals : List String) (spec : Spec) : Prop where
  names : Names spec
  plan : Nonempty (Plan globals spec)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
