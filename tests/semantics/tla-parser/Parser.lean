module

import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
import all Silmaril.Logic.Temporal.TLA.Surface.Examples
meta import all Silmaril.Logic.Temporal.TLA.Surface.Examples
import Silmaril.ProofFormats.TLA.SurfaceSExp.Defs
meta import Silmaril.ProofFormats.TLA.SurfaceSExp.Defs

open Silmaril.Logic.Temporal.TLA.Surface
open Silmaril.Logic.Temporal.TLA.Surface.Parser
open Silmaril.Logic.Temporal.TLA.Surface.Examples (boundedQueue)
open Silmaril.ProofFormats.TLA.SurfaceSExp (encodeModule)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def requireParsed {α : Type} (label : String) (result : Except Diagnostic α) : IO α :=
  match result with
  | .ok parsed => pure parsed
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def expr (source : String) : IO Expr := requireParsed source (parseExpr source)

private def definitionBody (parsed : Module) (name : String) : IO Expr := do
  for unit in parsed.units do
    if let .definition (.operator _ (.ident head _) body) := unit then
      if head == name then return body
  throw (IO.userError s!"{parsed.name}: missing definition {name}")

private def checkOperators : IO Unit := do
  match ← expr "-x^2 + y * z" with
  | .infix (.symbol "+") (.prefix .minus (.infix (.symbol "^") _ _)) (.infix (.symbol "*") _ _) => pure ()
  | value => throw (IO.userError s!"unexpected precedence: {reprStr value}")
  match ← expr "a $ b :> c" with
  | .infix (.symbol ":>") (.infix (.symbol "$") _ _) _ => pure ()
  | value => throw (IO.userError s!"unexpected interval precedence: {reprStr value}")
  match ← expr "a /\\ b \\land c" with
  | .infix (.symbol "\\land") (.infix (.symbol "/\\") _ _) _ => pure ()
  | value => throw (IO.userError s!"unexpected alias associativity: {reprStr value}")
  match ← expr "(A \\times B) \\X C × D" with
  | .cartesian [.cartesian [_, _], _, _] => pure ()
  | value => throw (IO.userError s!"unexpected Cartesian factors: {reprStr value}")
  match ← expr "f.a[i,j]'.b[<<i,j>>]" with
  | .index (.field (.postfix .prime (.index (.field _ "a") [_, _])) "b") [.tuple [_, _]] => pure ()
  | value => throw (IO.userError s!"unexpected indexing/selection: {reprStr value}")
  match ← expr "f'[i]''" with
  | .postfix .prime (.postfix .prime (.index (.postfix .prime _) [_])) => pure ()
  | value => throw (IO.userError s!"unexpected postfix chain: {reprStr value}")
  match ← expr "F(1..12, 001 . 0020, \\hA5, (a / b) * c, \"雪\\t\\\"\")" with
  | .ref (.operator (.ident "F"))
      [.expr (.infix (.symbol "..") (.literal (.natural 1)) (.literal (.natural 12))),
       .expr (.literal (.decimal 1 "0020")), .expr (.literal (.natural 165)),
       .expr (.infix (.symbol "*") (.infix (.symbol "/") _ _) _),
       .expr (.literal (.string "雪\t\""))] [] => pure ()
  | value => throw (IO.userError s!"unexpected literals/applications: {reprStr value}")

private def checkJunctions : IO Unit := do
  match ← expr "  /\\ \\/ A\n     \\/ B\n  ∧ C\n    /\\ D" with
  | .junction .conjunction [.junction .disjunction [_, _], .infix (.symbol "/\\") _ _] => pure ()
  | value => throw (IO.userError s!"unexpected nested list/continuation: {reprStr value}")
  match ← expr "  /\\ A\n  \\/ B" with
  | .infix (.symbol "\\/") (.junction .conjunction [_]) _ => pure ()
  | value => throw (IO.userError s!"unexpected same-column kind change: {reprStr value}")
  match ← expr "  /\\ A\n /\\ B\n   /\\ C" with
  | .infix (.symbol "/\\") (.infix (.symbol "/\\") (.junction .conjunction [_]) _) _ => pure ()
  | value => throw (IO.userError s!"unexpected dedent: {reprStr value}")
  match ← expr "\t/\\ IF A THEN B\r\n\t     ELSE C\r\n        /\\ D" with
  | .junction .conjunction [.ifThenElse _ _ _, _] => pure ()
  | value => throw (IO.userError s!"unexpected tab alignment: {reprStr value}")

private def checkConstructs : IO Unit := do
  match ← expr "M(x)!Op(y)!1!<<" with
  | .ref (.operator (.ident "M")) [.expr _]
      [.named (.ident "Op") [.expr _], .structural (.operand 1), .structural .left] => pure ()
  | value => throw (IO.userError s!"unexpected qualified reference: {reprStr value}")
  match ← expr "F(+, LAMBDA x,y: x + y)" with
  | .ref (.operator (.ident "F"))
      [.symbolic (.infix (.symbol "+")), .lambda ["x", "y"] (.infix (.symbol "+") _ _)] [] => pure ()
  | value => throw (IO.userError s!"unexpected operator arguments: {reprStr value}")
  match ← expr "LET RECURSIVE F(_) F(x) == [r EXCEPT !.f[x, 2] = @] IN F(0)" with
  | .letIn [.recursive [.ident "F" 1], .definition (.operator .ordinary (.ident "F" [.ident "x" 0])
      (.except _ [⟨[.field "f", .index [_, .literal (.natural 2)]], .oldValue⟩]))]
      (.ref (.operator (.ident "F")) [.expr (.literal (.natural 0))] []) => pure ()
  | value => throw (IO.userError s!"unexpected LET or EXCEPT: {reprStr value}")
  match ← expr "\\A <<x,y>> \\in S, z,w \\in T: CHOOSE u: u = z" with
  | .rigidQuant .forall (.bounded [⟨.tuple ["x", "y"], _⟩, ⟨.names ["z", "w"], _⟩])
      (.choose (.ident "u") none (.infix (.symbol "=") _ _)) => pure ()
  | value => throw (IO.userError s!"unexpected quantifier/CHOOSE shape: {reprStr value}")
  match ← expr "WF_M!F(i)(A) /\\ SF_<<x,y>>(B)" with
  | .infix (.symbol "/\\") (.fairness .weak (.ref _ [] [.named (.ident "F") [.expr _]]) _)
      (.fairness .strong (.tuple [_, _]) _) => pure ()
  | value => throw (IO.userError s!"unexpected fairness form: {reprStr value}")

private def checkDiagnostics : IO Unit := do
  let cases := [
    ("a ∧\r\n\t)", DiagnosticKind.syntax, ⟨8, 2, 9⟩, ⟨9, 2, 10⟩, "expression"),
    ("a * b / c", .precedence, ⟨6, 1, 7⟩, ⟨7, 1, 8⟩, "precedence conflict"),
    ("[]x'", .precedence, ⟨3, 1, 4⟩, ⟨4, 1, 5⟩, "precedence conflict"),
    ("a (*\n", .lexical, ⟨2, 1, 3⟩, ⟨5, 2, 1⟩, "unterminated block comment"),
    ("\"bad\\q\"", .lexical, ⟨4, 1, 5⟩, ⟨6, 1, 7⟩, "invalid string escape"),
    ("  /\\ (x'\n  )", .syntax, ⟨11, 2, 3⟩, ⟨12, 2, 4⟩, "outside the active junction"),
    ("a b", .syntax, ⟨2, 1, 3⟩, ⟨3, 1, 4⟩, "after complete input"),
    ("x +", .syntax, ⟨3, 1, 4⟩, ⟨3, 1, 4⟩, "expression"),
    ("<1>a", .syntax, ⟨0, 1, 1⟩, ⟨4, 1, 5⟩, "outside a hierarchical proof")]
  for (source, kind, start, stop, message) in cases do
    match parseExpr source with
    | .error actual =>
      check (actual.kind == kind && actual.span == ⟨start, stop⟩ &&
        actual.message.contains message) s!"unexpected diagnostic: {reprStr actual}"
    | .ok actual => throw (IO.userError s!"expected rejection of {source}: {reprStr actual}")

private def checkAssignments (boundedPath bitPath : System.FilePath) : IO Unit := do
  let bounded ← requireParsed "BoundedCounter" (parseModule (← IO.FS.readFile boundedPath))
  check (bounded.name == "BoundedCounter" && bounded.units.length == 5) "BoundedCounter module"
  check (bounded.extendsModules == ["Integers", "Sequences", "FiniteSets", "TLC", "Apalache", "Variants"])
    "BoundedCounter EXTENDS"
  match ← definitionBody bounded "step" with
  | .infix (.symbol "/\\") (.infix (.symbol "<") _ (.literal (.natural 2)))
      (.infix (.symbol ":=") (.postfix .prime (.ref (.operator (.ident "n")) [] []))
        (.infix (.symbol "+") _ (.literal (.natural 1)))) => pure ()
  | value => throw (IO.userError s!"BoundedCounter step: {reprStr value}")
  let bits ← requireParsed "BitPair" (parseModule (← IO.FS.readFile bitPath))
  check (bits.name == "BitPair" && bits.units.length == 6) "BitPair module"
  match ← definitionBody bits "step" with
  | .rigidQuant .exists (.bounded [⟨.names ["flip"], .setEnum [_, _]⟩])
      (.infix (.symbol "/\\")
        (.infix (.symbol ":=") (.postfix .prime (.ref (.operator (.ident "x")) [] [])) _)
        (.infix (.symbol ":=") (.postfix .prime (.ref (.operator (.ident "y")) [] []))
          (.ifThenElse _ (.infix (.symbol "-") _ _) _))) => pure ()
  | value => throw (IO.userError s!"BitPair step: {reprStr value}")

private def name (id : Ident) (args : List Expr := []) : Expr :=
  .ref (.operator (.ident id)) (args.map .expr) []

private def stepRef (level : StepRefLevel) (id : Ident) : Expr :=
  .ref (.step ⟨level, id⟩) [] []

private def proofStepsModule : Module :=
  let truth := name "TRUE"
  let natural := fun n => Expr.literal (.natural n)
  let prep := stepRef (.explicit 3) "prep"
  let currentPrep := stepRef .current "prep"
  let tupleBound : Bound := ⟨.tuple ["x", "y"], name "S"⟩
  let sufficesProof := Proof.steps [⟨⟨.current, none⟩, .have truth⟩]
    ⟨.explicit 5, none⟩ (some .obvious)
  let caseProof := Proof.steps
    [⟨⟨.next, none⟩, .suffices
      (.assumeProve .plain [.newBoundConstant "k" (name "S")] .plain (name "P" [name "k"]))
      (some sufficesProof)⟩] ⟨.explicit 4, none⟩ none
  let proof := Proof.steps
    [ ⟨⟨.explicit 3, some "prep"⟩, .define
        [ .operator .local (.ident "F" [.ident "x" 0]) (name "x"),
          .function .ordinary "G" [⟨.names ["y"], name "S"⟩] (name "F" [name "y"]) ]⟩,
      ⟨⟨.current, some "plain"⟩, .define
        [ .namedInstance .ordinary "H" [] ⟨"M", [⟨.ident "C", .symbolic (.infix (.symbol "+"))⟩]⟩,
          .operator .ordinary (.ident "J" []) (name "F" [natural 0]) ]⟩,
      ⟨⟨.explicit 3, none⟩, .instantiation ⟨"M", [⟨.ident "C", .expr prep⟩]⟩⟩,
      ⟨⟨.explicit 3, none⟩, .have (.ref (.step ⟨.explicit 3, "prep"⟩) [.expr (natural 1)]
        [.named (.ident "Label") [.expr (natural 2)], .structural (.operand 1)])⟩,
      ⟨⟨.explicit 3, none⟩, .take (.bounded [tupleBound, ⟨.names ["z", "w"], name "V"⟩])⟩,
      ⟨⟨.explicit 3, none⟩, .witness
        [ .infix (.symbol "\\in") (.tuple [name "x", name "y"]) (name "S"),
          .ref (.step ⟨.current, "prep"⟩) [] [.structural .body] ]⟩,
      ⟨⟨.current, none⟩, .pick (.unbounded ["p", "q"]) (name "P" [name "p", name "q"])
        (some (.byFacts true ⟨[.moduleName "M", .expr currentPrep], [.expr prep, .moduleName "N"]⟩))⟩,
      ⟨⟨.explicit 3, some "case_label"⟩, .caseOf (name "C") (some caseProof)⟩,
      ⟨⟨.explicit 3, none⟩, .directive (.use true ⟨[.expr prep], [.expr (name "H")]⟩)⟩,
      ⟨⟨.explicit 3, none⟩, .directive (.hide ⟨[], [.expr (name "G")]⟩)⟩,
      ⟨⟨.explicit 3, some "last"⟩, .assert (.assumeProve .plain [.statement (.expr truth)] .plain truth)
        (some (.steps [] ⟨.explicit 9, none⟩ (some .omitted)))⟩ ]
    ⟨.explicit 3, some "end"⟩
    (some (.steps [] ⟨.next, none⟩ (some (.byFacts false ⟨[.expr (stepRef .current "unknown")], []⟩))))
  ⟨"ProofSteps", [],
    [ .theoremDecl ⟨some "T", .expr truth, some proof⟩,
      .theoremDecl ⟨some "U", .expr truth, some (.steps [] ⟨.current, none⟩ none)⟩ ]⟩

private def checkUpstreamShape (parsed : Module) : IO Unit := do
  if parsed.name == "HourClock" then
    match parsed.units with
    | [.variables ["hr"], .definition _, .definition _, .definition _,
        .theoremDecl ⟨none, .expr (.infix (.symbol "=>") _ (.prefix .always _)), none⟩] =>
      match ← definitionBody parsed "HC" with
      | .infix (.symbol "/\\") _ (.prefix .always (.action .square _ _)) => pure ()
      | value => throw (IO.userError s!"HourClock HC: {reprStr value}")
    | units => throw (IO.userError s!"HourClock units: {reprStr units}")
  else if parsed.name == "LiveHourClock" then
    check (parsed.units.length == 7) "LiveHourClock unit count"
    match ← definitionBody parsed "LSpec", ← definitionBody parsed "AlwaysTick",
        ← definitionBody parsed "PostCondition" with
    | .infix (.symbol "/\\") _ (.fairness .weak _ _),
      .prefix .always (.prefix .eventually (.action .angle _ _)),
      .infix (.symbol "=") _ (.record [⟨"action", .setEnum events⟩, ⟨"state", .setEnum states⟩]) =>
      check (events.length == 12 && states.length == 12) "LiveHourClock trace fixture"
    | _, _, _ => throw (IO.userError "LiveHourClock expression shapes")
  else if parsed.name == "DieHard" then
    check (parsed.units.length == 16) "DieHard unit count"
    match ← definitionBody parsed "Init", ← definitionBody parsed "FixWater" with
    | .junction .conjunction [_, _, _, _], .junction .disjunction items =>
      check (items.length == 6 && items.all (fun
        | .junction .conjunction [_, _, _] | .junction .conjunction [_, _, _, _] => true
        | _ => false)) "DieHard nested junction lists"
    | _, _ => throw (IO.userError "DieHard expression shapes")

private def checkCorpus : List String → IO Unit
  | [] => pure ()
  | file :: expected :: rest => do
    let source ← IO.FS.readFile file
    match parseModule source with
    | .ok parsed =>
      check (expected == "accept") s!"{file}: unexpectedly accepted"
      let filename := (System.FilePath.mk file).fileName
      if filename == some "BoundedQueue.tla" || filename == some "ProofSteps.tla" then
        let tree := if filename == some "BoundedQueue.tla" then boundedQueue else proofStepsModule
        check (decide (encodeModule parsed = encodeModule tree)) s!"{file}: wrong tree\n{reprStr parsed}"
      else
        checkUpstreamShape parsed
    | .error error =>
      let actual := if error.kind == .unsupported then "unsupported" else "reject"
      check (actual == expected) s!"{file}: {reprStr error}"
    checkCorpus rest
  | _ => throw (IO.userError "supply path/verdict pairs")

private def checkModuleShape : IO Unit := do
  let source := "(* lead (* nested *) *)\n---- MODULE Parent ----\n\
    EXTENDS Base\nCONSTANT C, F(_)\n---- MODULE Child ----\n\
    VARIABLE v\n====\nLOCAL I(x) == INSTANCE Child WITH v <- x\n\
    LEMMA T == ASSUME NEW x \\in C, NEW VARIABLE w PROVE F(x) BY ONLY F(x) DEF F\n\
    ==== \\* trailing comment"
  let parsed ← requireParsed "module with nested unit and proof" (parseModule source)
  match parsed with
  | ⟨"Parent", ["Base"], [.constants [.ident "C" 0, .ident "F" 1],
      .submodule ⟨"Child", [], [.variables ["v"]]⟩,
      .definition (.namedInstance .local "I" [.ident "x" 0] ⟨"Child", [⟨.ident "v", _⟩]⟩),
      .theoremDecl ⟨some "T", .assumeProve .plain [.newBoundConstant "x" _, .newVariable "w"] .plain _,
        some (.byFacts true ⟨[.expr _], [.expr _]⟩)⟩]⟩ => pure ()
  | value => throw (IO.userError s!"unexpected module shape: {reprStr value}")

public def main (args : List String) : IO Unit := do
  checkOperators
  checkJunctions
  checkConstructs
  checkDiagnostics
  checkModuleShape
  let fixtures := System.FilePath.mk "tests/semantics/tla-quint"
  checkAssignments (fixtures / "BoundedCounter.tla") (fixtures / "BitPair.tla")
  checkCorpus args
  IO.println s!"Native TLA+ parser regressions passed ({args.length / 2} corpus modules)"
