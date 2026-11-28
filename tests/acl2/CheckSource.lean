module

import Silmaril.ProofFormats.ACL2.Defs
import Silmaril.Logic.ACL2.Books.Examples
meta import Silmaril.ProofFormats.ACL2.Defs
meta import Silmaril.Logic.ACL2.Books.Examples

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Examples Silmaril.ProofFormats.ACL2

private def requireOk {α : Type} (label : String) (result : Except SourceError α) : IO α :=
  match result with
  | .ok accepted => pure accepted
  | .error err => throw (IO.userError s!"{label}: {repr err}")

private def reject {W V : World} (label : String) (source : String)
    (includes : List String) (book : Book W V) (acceptsError : SourceError → Bool) : IO Unit :=
  match admitSource source includes book with
  | .error err =>
    unless acceptsError err do throw (IO.userError s!"{label}: unexpected {repr err}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly admitted")

/-- Match the authored fixture against the checked Lean books and exercise rejection paths. -/
public def main : IO Unit := do
  let defs ← IO.FS.readFile "tests/acl2/books/acl2-definitions.lisp"
  let thms ← IO.FS.readFile "tests/acl2/books/acl2-theorems.lisp"
  let dependencies := ["acl2-definitions"]
  let base ← requireOk "definition book" (admitSource defs [] definitionsBook)
  let later ← requireOk "theorem book" (admitSource thms dependencies theoremsBook)
  let combined : Book World.initial exampleWorld := base.book.includeBook later.book
  let _checked : exampleWorld.Checked := combined.checked (World.checked_bare _)
  reject "reader evaluation" (defs ++ "\n#.(car nil)") [] definitionsBook fun
    | .reader => true
    | _ => false
  reject "wrong dependency" thms ["other-book"] theoremsBook fun
    | .includeMismatch _ _ => true
    | _ => false
  reject "wrong arity" (thms.replace "(silmaril-first (cons head tail))" "(silmaril-first head tail)")
    dependencies theoremsBook fun
    | .eventMismatch => true
    | _ => false
  reject "changed variable sharing" (thms.replace "(cons head tail)) head" "(cons head tail)) tail")
    dependencies theoremsBook fun
    | .eventMismatch => true
    | _ => false
  reject "rebound formals" (defs.replace "(object)" "(object object)") [] definitionsBook fun
    | .unsupportedBook => true
    | _ => false
  IO.println "Matched two authored ACL2 books to checked Lean events and rejected five invalid inputs."
