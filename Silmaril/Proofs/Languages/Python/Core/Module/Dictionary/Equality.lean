module

public import Silmaril.Languages.Python.Core.Module.Dictionary.Defs

public section

namespace Silmaril.Proofs.Languages.Python.Core.Module.Dictionary

open Silmaril.Languages.Python.Core.Module (Value)
open Silmaril.Languages.Python.Core.Module.TupleDispatch (Element)
open Silmaril.Languages.Python.Core.Module.Dictionary

theorem equalContents_self (entries : List Entry) : equalContents entries entries = true := by
  have exactAtom (atom : Atom) : atom.equal atom = true := by
    cases atom with
    | scalar a =>
      cases a with
      | none => rfl
      | int n => simp [Element.equal, Value.equal, Value.asInt?]
      | bool b => cases b <;> rfl
    | text a => simp [Element.equal]
  have matching : entries.all (fun entry => entries.any (entry.equal ·)) = true :=
    List.all_eq_true.mpr fun entry member =>
      List.any_eq_true.mpr ⟨entry, member, by simp [Entry.equal, exactAtom]⟩
  simp only [equalContents, matching]
  rfl

end Silmaril.Proofs.Languages.Python.Core.Module.Dictionary
