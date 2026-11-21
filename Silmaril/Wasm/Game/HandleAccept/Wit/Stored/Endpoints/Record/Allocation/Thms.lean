module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Allocation.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordAllocation

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Field

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon

/-- The root's allocation check at the linked width entails the allocation
preconditions of every active compiled descendant. This is a static value
fact, not a range, authority, or allocator-return guarantee. -/
theorem Descendant.fits {root child : Field} {type : TypeOf}
    (path : Descendant root child) (layout : root.LayoutMatches type)
    (quirks : Quirks) (encoding : StringEncoding) (width : AddrType)
    (admitted : Lower.fits quirks encoding width type root.value = true) :
    child.LayoutMatches child.type ∧ Lower.fits quirks encoding width child.type child.value = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordAllocation.descendant quirks encoding width path
    layout admitted

/-- String leaves, including map keys, can start the canonical string plan
without re-establishing its static precondition after each ancestor. -/
theorem Descendant.string_pre {root : Field} {type : TypeOf} (payload : Payload (.prim .string))
    {str : Value.StrVal} (represents : payload.val = .string str)
    (path : Descendant root (.data (.prim .string) payload)) (layout : root.LayoutMatches type)
    (quirks : Quirks) (encoding : StringEncoding) (width : AddrType)
    (admitted : Lower.fits quirks encoding width type root.value = true) :
    StoreStringPre quirks encoding width str := by
  have fits := (path.fits layout quirks encoding width admitted).2
  simpa only [Field.type, Field.value, represents, Lower.fits, decide_eq_true_eq] using fits

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.Field
