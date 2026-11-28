module

import Silmaril.Logic.ACL2.Standard.Thms
import Silmaril.Logic.ACL2.Books.Examples
meta import Silmaril.Logic.ACL2.Standard.Defs
meta import Silmaril.Logic.ACL2.Books.Examples

open Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Examples

example : World.initial.signature.resolve firstName 1 = none := rfl
example : definedWorld.signature.resolve firstName 2 = none := rfl
example : definedWorld.signature.resolve firstName 1 = some firstSymbol := rfl
example : provedWorld.presentation = definedWorld.presentation := rfl
example : exampleWorld.theoremAt firstConsName = some firstCons := rfl

private inductive Value
  | nil
  | truth
  | pair (x y : Value)
  deriving DecidableEq

private def primitives : Primitives where
  Value := Value
  nil := .nil
  truth := .truth
  cons := .pair
  car := fun | .pair x _ => x | _ => .nil
  cdr := fun | .pair _ y => y | _ => .nil
  consp := fun | .pair _ _ => true | _ => false
  truth_ne_nil := by intro h; cases h
  consp_nil := rfl
  consp_truth := rfl
  consp_cons := fun _ _ => rfl
  car_cons := fun _ _ => rfl
  cdr_cons := fun _ _ => rfl
  car_atom := fun x h => by cases x <;> first | rfl | cases h
  cdr_atom := fun x h => by cases x <;> first | rfl | cases h

private def initialModel : Model World.initial.signature :=
  ⟨primitives, fun f => by cases f.property⟩

example : ∃ M : Model exampleWorld.signature, exampleWorld.Models M := by
  have h : World.initial.Models initialModel := (World.valid_bare _) _ fun _ ⟨_, _, _, hb, _⟩ => by cases hb
  obtain ⟨M, hM, _⟩ := exampleBook.expand initialModel h
  exact ⟨M, hM⟩

/-- Emit the checked example as two ACL2 books, with the dependency expressed natively. -/
public def main : List String → IO Unit
  | [dir] => do
    let output : System.FilePath := dir
    IO.FS.createDirAll output
    IO.FS.writeFile (output / "acl2-definitions.lisp") (Standard.source definitionsBook)
    IO.FS.writeFile (output / "acl2-theorems.lisp")
      ("(in-package \"ACL2\")\n\n(include-book \"acl2-definitions\")\n\n" ++
        String.intercalate "\n\n" (Standard.events theoremsBook) ++ "\n")
  | _ => throw (IO.userError "usage: BookSource.lean OUTPUT_DIRECTORY")
