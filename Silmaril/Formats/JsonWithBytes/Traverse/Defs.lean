module

public import Silmaril.Formats.JsonWithBytes.Defs

@[expose] public section

namespace Silmaril.Formats.JsonWithBytes

/-- Traverse ordered syntax without changing its shape or member order. -/
def traverse? {Key Key' Input Output : Type} (key : Key → Option Key')
    (scalar : Input → Option Output) : {index : JsonIx} →
    RawSyn Key Input index → Option (RawSyn Key' Output index)
  | _, .scalar value => .scalar <$> scalar value
  | _, .list items => .list <$> traverse? key scalar items
  | _, .map entries => .map <$> traverse? key scalar entries
  | _, .nil => some .nil
  | _, .cons value tail => return .cons (← traverse? key scalar value) (← traverse? key scalar tail)
  | _, .objNil => some .objNil
  | _, .objCons name value tail =>
    return .objCons (← key name) (← traverse? key scalar value) (← traverse? key scalar tail)

/-- Reject duplicate object keys (rather than choosing one of the values). -/
def uniqueKeys {Key Atom : Type} [DecidableEq Key] : {index : JsonIx} →
    RawSyn Key Atom index → Bool
  | _, .scalar _ => true
  | _, .list items => uniqueKeys items
  | _, .map entries => decide entries.keys.Nodup && uniqueKeys entries
  | _, .nil => true
  | _, .cons value tail => uniqueKeys value && uniqueKeys tail
  | _, .objNil => true
  | _, .objCons _ value tail => uniqueKeys value && uniqueKeys tail

end Silmaril.Formats.JsonWithBytes
