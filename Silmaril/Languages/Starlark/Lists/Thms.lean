module

public import Silmaril.Languages.Starlark.Lists.Denotation.Defs
public import Silmaril.Languages.Starlark.Lists.Freeze.Defs
public import Silmaril.Languages.Starlark.Lists.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.Dictionary
import Silmaril.Proofs.Languages.Starlark.Lists.Eval
import Silmaril.Proofs.Languages.Starlark.Lists.Freeze

public section

namespace Silmaril.Languages.Starlark.Lists

/-- Evaluation agrees with the denotation on both success and failure states. -/
theorem eval_iff_denote {α : Type} (code : Code α) (state : State) (out : Outcome α) :
    Eval state code out ↔ denote code state = out :=
  ⟨Proofs.Languages.Starlark.Lists.denote_eq_of_eval,
    fun h => h ▸ Proofs.Languages.Starlark.Lists.eval_denote code state⟩

/-- Freezing is the unique pointwise update prescribed by live graph reachability. -/
theorem freezes_iff_freeze (heap : Heap) (roots : List Address) (after : Heap) :
    Freezes heap roots after ↔ heap.freeze roots = after :=
  ⟨Proofs.Languages.Starlark.Lists.eq_freeze_of_freezes,
    fun h => h ▸ Proofs.Languages.Starlark.Lists.freezes_freeze heap roots⟩

/-- An update preserves iteration order and an insertion adds its key at the end. -/
theorem putEntry_keys (entry : Entry) (entries : List Entry) :
    (putEntry entry entries).map Entry.key =
      if (findEntry entry.keyCode entries).isSome then entries.map Entry.key
      else entries.map Entry.key ++ [entry.key] :=
  Proofs.Languages.Starlark.Lists.putEntry_keys entry entries

/-- Freezing preserves key eligibility and the canonical encoding of every key. -/
theorem keyOf_freeze (state : State) (roots : List Value) (value : Value) :
    (state.freeze roots).keyOf value = state.keyOf value :=
  Proofs.Languages.Starlark.Lists.keyOf_freeze state roots value

/-- A frozen cell rejects an edit without inspecting the edit result. -/
theorem editCell_frozen (state : State) (address : Address)
    (edit : Contents → Except Error Contents) {cell : Cell}
    (found : state.heap[address]? = some cell) (frozen : cell.frozen = true) :
    editCell address edit state = .error (.frozen address) state :=
  Proofs.Languages.Starlark.Lists.editCell_frozen state address edit found frozen

end Silmaril.Languages.Starlark.Lists
