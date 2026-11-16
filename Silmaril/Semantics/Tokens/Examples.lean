module

public import Silmaril.Semantics.Tokens.Thms

/-!
# Token streams: examples

`lines sep` frames a symbol stream into items separated by `sep`, as line-delimited
formats do. The item contents are left uninterpreted: parsing each item is the job of a
format-specific token language. The pending item is flushed only at the end of input.
-/

@[expose] public section

namespace Silmaril.Streams.TokensExamples

open Silmaril.Streams

/-- Frame a stream into `sep`-terminated items; the state is the pending item (reversed). -/
def lines {α : Type} [DecidableEq α] (sep : α) : Transducer (List α) α (List α) where
  init := []
  step buf a := if a = sep then ([], [buf.reverse]) else (a :: buf, [])
  flush buf := if buf = [] then [] else [buf.reverse]

/-- Committed items exclude the unterminated last item; `tokenize` includes it. -/
example : (lines 0).emitted [1, 2, 0, 3, 0, 4] = [[1, 2], [3]] := by decide
example : (lines 0).tokenize [1, 2, 0, 3, 0, 4] = [[1, 2], [3], [4]] := by decide

/-- Chunk boundaries inside an item do not matter. -/
example : (lines 0).emitted ([1] ++ [2, 0, 3] ++ [0]) = (lines 0).emitted [1, 2, 0, 3, 0] := by
  decide

end Silmaril.Streams.TokensExamples
