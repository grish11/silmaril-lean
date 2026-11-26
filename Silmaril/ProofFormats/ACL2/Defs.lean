module

public import Silmaril.Formats.SExp.CommonLisp.Defs
public import Silmaril.Logic.ACL2.Standard.Defs

public section

namespace Silmaril.ProofFormats.ACL2

open Silmaril.Formats Silmaril.Logic.ACL2

private abbrev Datum := CommonLisp.Datum

private def properList? : Datum → Option (List Datum)
  | .nil => some []
  | .cons x xs => (x :: ·) <$> properList? xs
  | .atom _ => none

private def functionName? : Datum → Option String
  | .atom (.symbol s) | .atom (.qualified "ACL2" s true) => some s
  | _ => none

private def variableName? : Datum → Option String
  | .atom (.symbol s) => if s == "T" || s == "NIL" then none else some s
  | _ => none

private inductive TermAtom where
  | var (index : Nat)
  | call (name : String)
  | truth
  deriving DecidableEq

private abbrev TermShape := SExp2 TermAtom

mutual

/-- Definition variables are indexed by formals and theorem variables by first occurrence. -/
private def readTerm (allowFree : Bool) : Datum → List String → Option (TermShape × List String)
  | .nil, vars | .atom (.symbol "NIL"), vars => some (.nil, vars)
  | .atom (.symbol "T"), vars => some (.atom .truth, vars)
  | .atom (.symbol s), vars =>
    if let some i := vars.idxOf? s then some (.atom (.var i), vars)
    else if allowFree then some (.atom (.var vars.length), vars ++ [s])
    else none
  | .cons head tail, vars => do
    let name ← functionName? head
    let (args, vars) ← readArgs allowFree tail vars
    return (.cons (.atom (.call name)) args, vars)
  | _, _ => none

private def readArgs (allowFree : Bool) : Datum → List String → Option (TermShape × List String)
  | .nil, vars => some (.nil, vars)
  | .cons arg rest, vars => do
    let (arg, vars) ← readTerm allowFree arg vars
    let (rest, vars) ← readArgs allowFree rest vars
    return (.cons arg rest, vars)
  | .atom _, _ => none

end

private inductive EventShape where
  | defun (name : String) (arity : Nat) (body : TermShape)
  | defthm (name : String) (statement : TermShape)
  deriving DecidableEq

private def readDefinition (name formals body : Datum) : Option EventShape := do
  let name ← functionName? name
  let vars ← (← properList? formals).mapM variableName?
  if vars.eraseDups.length ≠ vars.length then none else
    return .defun name vars.length (← readTerm false body vars).1

private def readTheorem (name statement : Datum) : Option EventShape := do
  return .defthm (← functionName? name) (← readTerm true statement []).1

private def readEvent (form : Datum) : Option EventShape :=
  match properList? form with
  | some [.atom (.symbol "DEFUN"), name, formals, body] => readDefinition name formals body
  | some [.atom (.symbol "DEFUN"), name, formals, decl, body] =>
    if CommonLisp.parse? "(declare (xargs :mode :logic))" = some decl then
      readDefinition name formals body
    else none
  | some [.atom (.symbol "DEFTHM"), name, statement] |
    some [.atom (.symbol "DEFTHM"), name, statement, .atom (.keyword "RULE-CLASSES"),
      .atom (.symbol "NIL")] => readTheorem name statement
  | _ => none

private def includePath? (form : Datum) : Option String :=
  match properList? form with
  | some [.atom (.symbol "INCLUDE-BOOK"), .atom (.string path)] => some path
  | _ => none

private def readBook (forms : List Datum) : Option (List String × List EventShape) := do
  let header :: rest := forms | none
  if properList? header ≠ some [.atom (.symbol "IN-PACKAGE"), .atom (.string "ACL2")] then none
  else
    let (includes, events) := rest.span fun form => (includePath? form).isSome
    return (includes.filterMap includePath?, ← events.mapM readEvent)

/-- Failures at the reader, source profile, dependency, or checked event boundary. -/
inductive SourceError where
  | reader
  | unsupportedBook
  | includeMismatch (expected actual : List String)
  | unsupportedCheckedBook
  | eventMismatch
  deriving Repr

/-- Read the ACL2-package source subset and compare its event names, arities and terms to an
already checked book. Variables may use different names if they preserve binding and sharing.
The include list records expected leading dependency paths in order. -/
def checkSource {W V : World} (source : String) (includes : List String) (book : Book W V) :
    Except SourceError Unit := do
  let some forms := CommonLisp.parseAll? source | throw .reader
  let some (actualIncludes, actual) := readBook forms | throw .unsupportedBook
  if actualIncludes ≠ includes then throw (.includeMismatch includes actualIncludes)
  let some (_, expected) := CommonLisp.parseAll? (Standard.source book) >>= readBook |
    throw .unsupportedCheckedBook
  if actual ≠ expected then throw .eventMismatch

/-- The source has been matched to explicit Lean derivations and the typed input/output worlds. -/
structure CheckedSource (source : String) (includes : List String) (W V : World) where
  book : Book W V
  matchProof : checkSource source includes book = .ok ()

/-- Admit source against a supplied checked book, retaining the source-match witness. -/
def admitSource {W V : World} (source : String) (includes : List String) (book : Book W V) :
    Except SourceError (CheckedSource source includes W V) :=
  match h : checkSource source includes book with
  | .ok () => .ok ⟨book, h⟩
  | .error err => .error err

end Silmaril.ProofFormats.ACL2
