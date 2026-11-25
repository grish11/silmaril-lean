module

import Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs
meta import Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-!
Scratch probe for #3042, not a DataElab layer. Supports only the Boolean
constructs used by the fixtures. Run with pinned Lake from the checkout.
-/

open Silmaril.Logic.Temporal.TLA
open Resolution

private inductive Endpoint where
  | source | target

private abbrev Suspended := Endpoint → Except String Bool
private abbrev Frame := List (BindingId × Suspended)
private abbrev Valuation := BindingId → Endpoint → Option Bool

private inductive Work where
  | expression (site : Site) (body : Surface.Expr)
  | apply (site : Site) (binding : BindingId) (actuals : List Suspended)

private def atBinding (checked : Instances.CheckedInstances) (moduleId : ModuleId) (name : Name) :
    Except String BindingId := do
  let some found := (checked.registry.moduleAt moduleId).bind (·.bindingAt name)
    | throw s!"Missing binding {moduleId} {reprStr name}"
  return found.id

private def errorAt (site : Site) (message : String) : Except String Bool :=
  throw s!"{message} at {reprStr site}"

private def builtin (site : Site) (endpoint : Endpoint) (name : Name) :
    List Suspended → Except String Bool
  | [] => match name with
    | .ident "TRUE" => pure true
    | .ident "FALSE" => pure false
    | _ => errorAt site s!"Unsupported nullary builtin {reprStr name}"
  | [arg] => match name with
    | .symbol .postfix "'" =>
      match endpoint with
      | .source => arg .target
      | .target => errorAt site "Second endpoint shift"
    | .symbol .prefix "\\lnot" => return !(← arg endpoint)
    | _ => errorAt site s!"Unsupported unary builtin {reprStr name}"
  | [left, right] => do
    let a ← left endpoint
    let b ← right endpoint
    match name with
    | .symbol .infix "=" => return a == b
    | .symbol .infix "/=" => return a != b
    | .symbol .infix "\\land" => return a && b
    | .symbol .infix "\\lor" => return a || b
    | _ => errorAt site s!"Unsupported binary builtin {reprStr name}"
  | _ => errorAt site "Unsupported builtin arity"

private def replay (fuel : Nat) (checked : Instances.CheckedInstances) (values : Valuation)
    (frame : Frame) (endpoint : Endpoint) (work : Work) : Except String Bool :=
  match fuel with
  | 0 => throw "Probe exhausted its recursion bound"
  | remaining + 1 => do
    let run := replay remaining checked values
    match work with
    | .expression site expr =>
      let some reference := (checked.registry.moduleAt site.moduleId).bind (·.referenceAt site.path)
        | errorAt site "Missing resolved reference"
      unless reference.role = .application do
        discard <| errorAt site "Operator-valued actual is outside the probe"
      let args ← match expr with
        | .ref (.operator _) args [] =>
          pure (args.zipIdx.map fun (arg, index) => (site.child (.argument index), arg))
        | .ref (.operator name) args selectors =>
          let some (_, segments) := qualifiedCall site name args selectors
            | throw s!"Unsupported qualified syntax at {reprStr site}"
          pure (qualifiedArguments segments)
        | .prefix _ arg | .postfix _ arg => pure [(site.child (.operand 0), .expr arg)]
        | .infix _ left right =>
          pure [(site.child (.operand 0), .expr left), (site.child (.operand 1), .expr right)]
        | _ => throw s!"Outside the Boolean probe at {reprStr site}"
      let actuals ← args.mapM fun (argSite, arg) =>
        match arg with
        | .expr body => pure (fun ep => run frame ep (.expression argSite body))
        | _ => throw s!"Operator-valued actual at {reprStr argSite}"
      run frame endpoint (.apply site reference.target actuals)
    | .apply site id actuals =>
      let some binding := checked.registry.findBinding id
        | errorAt site s!"Unknown binding {reprStr id}"
      unless binding.slots = List.replicate actuals.length Slot.expression do
        discard <| errorAt site s!"Wrong expression arity for {reprStr id}"
      if let some value := frame.lookup id then
        return ← value endpoint
      if let some (plan, member) := checked.memberAt id then
        let (namespaceArgs, memberArgs) := actuals.splitAt plan.parameters.length
        let hostFrame := plan.parameters.zip namespaceArgs ++ frame
        let substituted : Frame := plan.substitutions.map fun (target, replacement) =>
          let captured := match replacement with
            | .expression host body => Work.expression host body
            | .binding hostId => Work.apply plan.site hostId []
          (target, fun ep => run hostFrame ep captured)
        return ← run (substituted ++ frame) endpoint (.apply site member.home memberArgs)
      match id, binding.kind with
      | .builtin name, _ => builtin site endpoint name actuals
      | _, .constant | _, .variable =>
        let some value := values id endpoint | errorAt site s!"Unexpected valuation key {reprStr id}"
        return value
      | .declared home, .operator =>
        let some mod := checked.registry.moduleAt home.moduleId
          | errorAt site s!"Missing home module {home.moduleId}"
        let some source := mod.source | errorAt site "Signature-only operator is outside the probe"
        let [.unit index] := home.path | errorAt site "Expected an ordinary home definition"
        let some (.definition (.operator _ _ body)) := source.units[index]?
          | errorAt site "Expected an operator body"
        let formals := actuals.zipIdx.map fun (arg, i) =>
          (BindingId.declared (home.child (.parameter i)), arg)
        run (formals ++ frame) endpoint (.expression (home.child .body) body)
      | _, _ => errorAt site s!"Unbound lexical key {reprStr id}"
termination_by structural fuel

private structure Fixture where
  id : ModuleId
  name : String
  units : String
  imports : ImportMap := []

private def registry (fixtures : List Fixture) : Except String Registry :=
  fixtures.mapM fun fixture => do
    let source := s!"---- MODULE {fixture.name} ----\n{fixture.units}\n====\n"
    let parsed ← (Surface.Parser.parseModule source).mapError reprStr
    return (fixture.id, .parsed parsed fixture.imports)

private def verify (fixtures : List Fixture) : Except String Instances.CheckedInstances := do
  (Instances.check (← registry fixtures) "root").mapError reprStr

private def run (checked : Instances.CheckedInstances) (values : Valuation) (name : Surface.Ident) :
    Except String Bool := do
  let target ← atBinding checked "root" (.ident name)
  let some summary := checked.levels.operatorAt target | throw s!"Missing checked level for {name}"
  unless summary.parameters.isEmpty && summary.result = .fixed .action &&
      summary.requirements.isEmpty do
    throw s!"Expected a closed action summary for {name}"
  replay 64 checked values [] .source (.apply ⟨"root", []⟩ target [])

private def nested : List Fixture := [
  ⟨"leaf", "Leaf",
    "VARIABLE cell\nLOCAL Read == cell\nSample(a) == (Read' # a) /\\ (Read = a')\nCurrent == Read", []⟩,
  ⟨"mid", "Middle",
    "VARIABLE bridge\nInner(b) == INSTANCE Leaf WITH cell <- bridge # b\n\
     Through(k) == Inner(TRUE)!Sample(k)", [("Leaf", "leaf")]⟩,
  ⟨"constant", "Constants", "CONSTANT C\nExpose == C", []⟩,
  ⟨"root", "Root",
    "VARIABLE x, y, z\nI(p) == INSTANCE Middle WITH bridge <- p /\\ x\n\
     J(p) == INSTANCE Middle WITH bridge <- p \\/ x\n\
     DirectI == I(y)!Inner(z)!Sample(x # z)\n\
     DirectJ == J(y)!Inner(z)!Sample(x # z)\n\
     HomeCall == I(y)!Through(x # z)\n\
     ActionRhs == INSTANCE Constants WITH C <- x'\nExplicitShift == ActionRhs!Expose\n\
     Relay == INSTANCE Leaf WITH cell <- I(y)!Inner(z)!Current\nPriorCall == Relay!Sample(x # z)",
    [("Middle", "mid"), ("Constants", "constant"), ("Leaf", "leaf")]⟩]

private def bools : List Bool := [false, true]

private def samples : List (Bool × Bool × Bool) :=
  bools.flatMap fun x => bools.flatMap fun y => bools.map fun z => (x, y, z)

private def nestedProbe : Except String Unit := do
  let checked ← verify nested
  let xi ← atBinding checked "root" (.ident "x")
  let yi ← atBinding checked "root" (.ident "y")
  let zi ← atBinding checked "root" (.ident "z")
  let i ← atBinding checked "root" (.qualified ["I", "Inner"] (.ident "Sample"))
  let j ← atBinding checked "root" (.qualified ["J", "Inner"] (.ident "Sample"))
  let some (iPlan, iMember) := checked.memberAt i | throw "Missing I plan"
  let some (jPlan, jMember) := checked.memberAt j | throw "Missing J plan"
  let some (innerPlan, _) := checked.memberAt iMember.home | throw "Missing nested plan"
  unless i ≠ j && iPlan.site ≠ jPlan.site && iMember.home = jMember.home &&
      iMember.argumentCounts = [1, 1, 1] && innerPlan.target = "leaf" do
    throw "Inconsistent home identities or qualified segment arities"
  for (sx, sy, sz) in samples do
    for (tx, ty, tz) in samples do
      let values : Valuation := fun id ep =>
        let (x, y, z) := match ep with | .source => (sx, sy, sz) | .target => (tx, ty, tz)
        if id = xi then some x else if id = yi then some y else if id = zi then some z else none
      let expected (sourceCell targetCell : Bool) : Bool :=
        (targetCell != (sx != sz)) && (sourceCell == (tx != tz))
      let cases :=
        [("DirectI", expected ((sy && sx) != sz) ((ty && tx) != tz)),
         ("DirectJ", expected ((sy || sx) != sz) ((ty || tx) != tz)),
         ("HomeCall", expected (!(sy && sx)) (!(ty && tx))),
         ("ExplicitShift", tx),
         ("PriorCall", expected ((sy && sx) != sz) ((ty && tx) != tz))]
      for (name, want) in cases do
        let actual ← run checked values name
        unless actual == want do
          throw s!"Bad replay for {name} at {(sx, sy, sz)} → {(tx, ty, tz)}"

private def sharedProbe : Except String Unit := do
  let checked ← verify [
    ⟨"common", "Common", "VARIABLE signal", []⟩,
    ⟨"leaf", "Leaf", "EXTENDS Common\nLOCAL Read == signal\nPeek == Read'",
      [("Common", "common")]⟩,
    ⟨"root", "Root", "EXTENDS Common\nINSTANCE Leaf\nOut == Peek",
      [("Common", "common"), ("Leaf", "leaf")]⟩]
  let signal ← atBinding checked "root" (.ident "signal")
  let some plan := checked.instanceAt ⟨"root", [.unit 0]⟩ | throw "Missing anonymous plan"
  let [(target, .binding host)] := plan.substitutions | throw "Expected one implicit replacement"
  unless target = signal && host = signal do throw "Implicit shared identity was lost"
  for a in bools do
    for b in bools do
      let values : Valuation := fun id ep =>
        if id = signal then some (match ep with | .source => a | .target => b) else none
      unless (← run checked values "Out") == b do throw "Implicit replacement did not shift"

private def nestedSharedProbe : Except String Unit := do
  let checked ← verify [
    ⟨"common", "Common", "VARIABLE signal", []⟩,
    ⟨"leaf", "Leaf", "EXTENDS Common\nLOCAL Read == signal\nPeek == Read'",
      [("Common", "common")]⟩,
    ⟨"mid", "Middle", "EXTENDS Common\nInner == INSTANCE Leaf\nThrough == Inner!Peek",
      [("Common", "common"), ("Leaf", "leaf")]⟩,
    ⟨"root", "Root",
      "EXTENDS Common\nOuter == INSTANCE Middle WITH signal <- ~signal\n\
       Direct == Outer!Inner!Peek\nIndirect == Outer!Through",
      [("Common", "common"), ("Middle", "mid")]⟩]
  let signal ← atBinding checked "root" (.ident "signal")
  for a in bools do
    for b in bools do
      let values : Valuation := fun id ep =>
        if id = signal then some (match ep with | .source => a | .target => b) else none
      for name in ["Direct", "Indirect"] do
        unless (← run checked values name) == !b do
          throw s!"Nested implicit replacement lost the outer frame at {name}"

private def certificateProbe : Except String Unit := do
  let a ← verify [⟨"root", "Root", "VARIABLE x\nOut == x", []⟩]
  let b ← verify [⟨"root", "Root", "VARIABLE x\nOut == x'", []⟩]
  let aid ← atBinding a "root" (.ident "Out")
  let bid ← atBinding b "root" (.ident "Out")
  let some state := a.levels.operatorAt aid | throw "No state summary"
  let some action := b.levels.operatorAt bid | throw "No action summary"
  unless aid = bid && state.result = .fixed .state && action.result = .fixed .action do
    throw "Expected equal site IDs across distinct graph receipts"
  let levelOnly ← (Levels.check a.registry).mapError reprStr
  unless (levelOnly.operatorAt aid).map Levels.OperatorSummary.result = some (.fixed .state) do
    throw "Rechecking an existing registry returned the wrong level"

private def argumentCeilings : Except String Unit := do
  let cases := [
    ("I(y')!Inner(z)!Sample(x # z)", "root"),
    ("I(y)!Inner(z')!Sample(x # z)", "mid"),
    ("I(y)!Inner(z)!Sample((x # z)')", "leaf")]
  for (call, owner) in cases do
    let inputs ← registry (nested.map fun fixture =>
      if fixture.id = "root" then { fixture with units := fixture.units ++ "\nBad == " ++ call }
      else fixture)
    match Instances.check inputs "root" with
    | .error (.levels error) =>
      let .failedRequirement requirement := error.kind
        | throw s!"Expected a call cap for {call}, got {reprStr error}"
      unless error.site = ⟨"root", [.unit 10, .body]⟩ &&
          requirement.origin.moduleId = owner &&
          requirement.condition = .atMost (.fixed .action) .state do
        throw s!"Wrong call cap for {call}: {reprStr error}"
    | _ => throw s!"Expected separate argument ceiling for {call}"

/--
error: invalid {...} notation, constructor for `Instances.CheckedInstances` is marked as private
-/
#guard_msgs in
example (left right : Instances.CheckedInstances) : Instances.CheckedInstances :=
  { left with levels := right.levels }

private def boundaryProbe : Except String Unit := do
  let makeInputs (units : String) := registry [
    ⟨"leaf", "Leaf", units, []⟩,
    ⟨"root", "Root", "INSTANCE Leaf", [("Leaf", "leaf")]⟩]
  match Instances.check (← makeInputs "THEOREM TRUE\nOut == TRUE") "root" with
  | .error (.resolution ⟨_, .unsupported .instanceTheorem⟩) => pure ()
  | _ => throw "Expected explicit rejection of theorem substitution"
  match Instances.check (← makeInputs "CONSTANT F(_)\nOut == F(TRUE)") "root" with
  | .error (.resolution ⟨_, .unsupported .operatorSubstitution⟩) => pure ()
  | _ => throw "Expected explicit rejection of operator-valued substitution"

public def main : IO Unit := do
  for (name, test) in [("nested and repeated", nestedProbe),
      ("implicit shared binding", sharedProbe), ("nested shared binding", nestedSharedProbe),
      ("certificate provenance", certificateProbe),
      ("separate argument ceilings", argumentCeilings),
      ("theorem and higher-order boundaries", boundaryProbe)] do
    match test with
    | .ok () => IO.println s!"PASS {name}"
    | .error msg => throw (IO.userError s!"{name}: {msg}")
