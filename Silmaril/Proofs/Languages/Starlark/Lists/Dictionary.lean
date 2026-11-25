module

public import Silmaril.Languages.Starlark.Lists.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists

open Silmaril.Languages.Starlark.Lists

theorem putEntry_keys (entry : Entry) (entries : List Entry) :
    (putEntry entry entries).map Entry.key =
      if (findEntry entry.keyCode entries).isSome then entries.map Entry.key
      else entries.map Entry.key ++ [entry.key] := by
  induction entries with
  | nil => rfl
  | cons old rest ih =>
    by_cases found : (old.keyCode == entry.keyCode) = true
    · simp [putEntry, findEntry, found]
    · simp [putEntry, findEntry, found] at *
      rw [ih]
      split <;> rfl

end Silmaril.Proofs.Languages.Starlark.Lists
