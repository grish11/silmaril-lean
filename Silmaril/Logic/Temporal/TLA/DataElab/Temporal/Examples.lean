module

meta import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Source admission and rejection cases for the temporal data bridge. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Temporal

open Resolution

private meta def registry (text : String) : Except String CheckedRegistry := do
  let source ← (Surface.Parser.parseModule text).mapError reprStr
  (resolveWith .levelSyntax [("root", .parsed source [])] "root").mapError reprStr

private meta def id (index : Nat) : BindingId := .declared ⟨"root", [.unit index]⟩
private meta def signature : ExternalSignature := fun _ => none

private meta def accepted : String := r"
---- MODULE Actions ----
VARIABLES x, y
Next == x' = y
Square == [Next]_<<x, y>>
Angle == <<Next>>_(IF x = 0 THEN y ELSE x)
Idle == UNCHANGED <<x, y>>
CanMove == ENABLED (Angle /\ ~Idle)
Spec == /\ CanMove
        /\ [][Next]_x
        /\ SF_x(Next)
Goal == (<>CanMove ~> []CanMove) <=> ~(<>FALSE \/ []FALSE)
====
"

private meta def acceptedShapes : Except String Bool := do
  let checked ← registry accepted
  let step := fun index => lowerAction checked [] signature 32 (id index)
  let .ok square := step 2 | throw "square action"
  let .ok angle := step 3 | throw "angle action"
  let .ok idle := step 4 | throw "unchanged action"
  let .ok enabled := lowerState checked [] signature 32 (id 5) | throw "enabled state predicate"
  let .ok spec := lowerFormula checked [] signature 32 (id 6) | throw "specification"
  let .ok goal := lowerFormula checked [] signature 32 (id 7) | throw "temporal Boolean formula"
  let .error (.bareAction _) := lowerFormula checked [] signature 32 (id 1)
    | throw "raw action promoted to formula"
  let .error (.wrongLevel _ .state .action) := lowerState checked [] signature 32 (id 2)
    | throw "square action selected as state predicate"
  match square.predicate, angle.predicate, idle.predicate, enabled.predicate, spec.form, goal.form with
  | .bracket .square (.data _) [_, _], .bracket .angle (.data _) [_], .unchanged [_, _],
    .enabled (.binary .and (.bracket .angle _ _) (.neg (.unchanged _))),
    .junction .conjunction [.state _, .alwaysBracket _ _, .fairness .strong _ _],
    .binary .equiv (.leadsTo (.eventually _) (.always _))
      (.neg (.binary .or (.eventually _) (.always _))) => return true
  | _, _, _, _, _, _ => throw "unexpected temporal lowering shape"

#guard match acceptedShapes with | .ok true => true | _ => false

private meta def badOperand (body : String) : Bool :=
  let text := "---- MODULE Bad ----\nVARIABLE x\nNext == x' = x\nF == " ++ body ++ "\n===="
  match registry text with
  | .ok checked =>
    match lowerFormula checked [] signature 32 (id 2) with
    | .error (.levels _) => true
    | _ => false
  | .error _ => false

#guard badOperand "[]Next"
#guard badOperand "<>[Next]_x"
#guard badOperand "[]<<Next>>_x"
#guard badOperand "ENABLED ([]TRUE)"
#guard badOperand "UNCHANGED (x')"
#guard badOperand "[][Next]_(x')"
#guard badOperand "WF_x([]TRUE)"
#guard badOperand "Next /\\ []TRUE"
#guard badOperand "Next ~> TRUE"
#guard badOperand r"\A a \in {x'} : [] (x = a)"
#guard badOperand r"\E a \in {[]TRUE} : <> (x = a)"
#guard badOperand r"\A a : [] (x' = a)"

private meta def rigidScopes : Except String Bool := do
  let checked ← registry r"
---- MODULE RigidScopes ----
VARIABLE x
Pair(p, q) == p = q
F == \A a, b \in {x}, c \in {0} : \E d \in {a} :
       [] (Pair(d, b) /\ (\E z \in {a} : Pair(z, c)))
G == \A a : [][x' = a]_<<x, a>>
====
"
  let lower := fun index => (lowerFormula checked [] signature 32 (id index)).mapError reprStr
  let f ← lower 2
  let g ← lower 3
  let .rigidQuant .forall 0 (some a)
    (.rigidQuant .forall 1 (some b) (.rigidQuant .forall 2 (some c)
      (.rigidQuant .exists 3 (some d) (.always (.state (.binary .and (.data lhs) (.data rhs))))))) :=
    f.form | throw "unexpected grouped or nested rigid binders"
  let .alwaysBracket (.data action) [_, observation] ←
    (match g.form with
    | .rigidQuant .forall 0 none body => pure body
    | _ => throw "expected an unbounded rigid binder")
    | throw "expected a quantified bracket action"
  match a.term, b.term, c.term, d.term, lhs.term, rhs.term, action.term, observation.term with
  | .enum [.flexible _], .enum [.flexible _], .enum [.numeral 0], .enum [.witness 0],
    .eq false (.witness 3) (.witness 1),
    .quant .exists 4 (some (.enum [.witness 0])) (.eq false (.witness 4) (.witness 2)),
    .eq false (.prime _ (.flexible _)) (.witness 0), .witness 0 => return true
  | _, _, _, _, _, _, _, _ => throw "rigid witnesses lost their lexical scope"

#guard match rigidScopes with | .ok true => true | _ => false

private meta def rejectsQuantifierSubstitution : Bool := Id.run do
  let .ok checked := registry r"
---- MODULE BadSubstitution ----
VARIABLE x
Quantify(S) == \A a \in S : [] (x = a)
F == Quantify({x'})
====
" | return false
  let .error (.levels ⟨site, .failedRequirement requirement⟩) :=
    lowerFormula checked [] signature 32 (id 2) | return false
  return site = ⟨"root", [.unit 2, .body]⟩ &&
    requirement.origin = ⟨"root", [.unit 1, .body, .bound 0, .domain]⟩ &&
    requirement.condition = .temporalQuantifierBound (.fixed .temporal) (.fixed .action)

#guard rejectsQuantifierSubstitution

#guard badOperand r"\EE h : h' = h"
#guard badOperand r"\AA h : [Next]_x"
#guard badOperand r"(\EE h : h = x)'"
#guard badOperand r"ENABLED (\EE h : h = x)"

private meta def rejectsFlexSubstitution : Bool := Id.run do
  let .ok checked := registry r"
---- MODULE BadFlexSubstitution ----
VARIABLE x
Hide(F) == \EE h : F
Bad == Hide(x' = x)
====
" | return false
  let .error (.levels ⟨site, .failedRequirement requirement⟩) :=
    lowerFormula checked [] signature 32 (id 2) | return false
  return site = ⟨"root", [.unit 2, .body]⟩ &&
    requirement.origin = ⟨"root", [.unit 1, .body, .body]⟩ &&
    requirement.condition = .nonAction (.fixed .action)

#guard rejectsFlexSubstitution

private meta def rejectsFlexName (body : String) (kind : Resolution.DiagnosticKind) : Bool := Id.run do
  let text := "---- MODULE Names ----\nVARIABLE x\nF == " ++ body ++ "\n===="
  let .ok source := Surface.Parser.parseModule text | return false
  let .error diagnostic := resolveWith .levelSyntax [("root", .parsed source [])] "root" | return false
  return diagnostic.kind = kind

#guard rejectsFlexName r"\EE h, h : h = h"
  (.conflictingName (.ident "h") (.declared ⟨"root", [.unit 1, .body, .binder 0]⟩))
#guard rejectsFlexName r"\AA x : x = x"
  (.conflictingName (.ident "x") (.declared ⟨"root", [.unit 0, .member 0]⟩))
#guard rejectsFlexName r"(\EE h : h = x) /\ (h = x)" (.unknownName (.ident "h"))

private meta def rejectsFlexSyntax (body : String) : Bool :=
  (Surface.Parser.parseModule ("---- MODULE Syntax ----\nF == " ++ body ++ "\n====")).isOk == false

#guard rejectsFlexSyntax r"\EE h \in {0} : TRUE"
#guard rejectsFlexSyntax r"\AA <<h, k>> : TRUE"

private meta def rejectsTupleBinder : Bool := Id.run do
  let .ok checked := registry "---- MODULE TupleBinder ----\nF == \\A <<a, b>> \\in {} : [] (a = b)\n===="
    | return false
  let .error (.data diagnostic) := lowerFormula checked [] signature 32 (id 0) | return false
  return diagnostic = ⟨⟨"root", [.unit 0, .body, .bound 0]⟩, .unsupported .tupleBinder⟩

#guard rejectsTupleBinder

-- A noncontributing primitive slot may accept an action operand. Retaining
-- that prime in an observation or quantifier domain would read the wrong endpoint.
private meta def rejectsRetainedPrime : Bool := Id.run do
  let text := r"
---- MODULE BadObservation ----
EXTENDS Lib
VARIABLE x
F == UNCHANGED Drop(x')
G == \A a \in Drop(x') : [] (x = a)
====
"
  let .ok source := Surface.Parser.parseModule text | return false
  let .ok checked := resolveWith .levelSyntax [
    ("root", .parsed source [("Lib", "lib")]),
    ("lib", .signature "Lib" [] [.operator (.ident "Drop") [.expression]])] "root" | return false
  let drop : BindingId := .declared ⟨"lib", [.member 0]⟩
  let levels : Levels.ExternalLevels := [(drop, ⟨.constant, [⟨.action, false⟩]⟩)]
  let admits : ExternalSignature := fun binding => if binding = drop then some 1 else none
  let .error (.primeInState site) := lowerAction checked levels admits 32 (id 1) | return false
  let .error (.primeInState rangeSite) := lowerFormula checked levels admits 32 (id 2) | return false
  return site = ⟨"root", [.unit 1, .body, .operand 0, .argument 0]⟩ &&
    rangeSite = ⟨"root", [.unit 2, .body, .bound 0, .domain, .argument 0]⟩

#guard rejectsRetainedPrime

private meta def rejectsTemporalPrimitive : Bool := Id.run do
  let text := "---- MODULE BadPrimitive ----\nEXTENDS Lib\nF == Drop(Future)\n===="
  let .ok source := Surface.Parser.parseModule text | return false
  let .ok checked := resolveWith .levelSyntax [
    ("root", .parsed source [("Lib", "lib")]),
    ("lib", .signature "Lib" [] [
      .operator (.ident "Drop") [.expression], .operator (.ident "Future") []])] "root" | return false
  let drop : BindingId := .declared ⟨"lib", [.member 0]⟩
  let future : BindingId := .declared ⟨"lib", [.member 1]⟩
  let levels : Levels.ExternalLevels :=
    [(drop, ⟨.constant, [⟨.temporal, false⟩]⟩), (future, ⟨.temporal, []⟩)]
  let admits : ExternalSignature := fun binding =>
    if binding = drop then some 1 else if binding = future then some 0 else none
  let .error (.temporalPrimitive binding) := lowerState checked levels admits 32 (id 0)
    | return false
  return binding = future

#guard rejectsTemporalPrimitive

end Silmaril.Logic.Temporal.TLA.DataElab.Temporal
