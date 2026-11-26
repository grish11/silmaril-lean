module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Defs

/-! Opt-in commutative add matching for shared entry reuse. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative

open Pure.SubZero (word)
open Pure.RightIdentityPass (wordProducers)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

/-- Match either orientation of the same two typed wires on this occurrence. -/
def matchesAt (p : Program inputs sigs [word]) (lhs rhs : SharedWord inputs sigs) (slot : Slot) : Bool :=
  EntryReuse.matchesAt p lhs rhs slot || EntryReuse.matchesAt p rhs lhs slot

/-- Admit only a word add whose unordered operand pair matches at both occurrences. -/
def check (p : Program inputs sigs [word]) (rep : EntryAdd p) : Bool :=
  match addOperands? rep.key with
  | none => false
  | some ⟨(lhs, rhs), _⟩ => matchesAt p lhs rhs .first && matchesAt p lhs rhs .second

/-- Select the first admitted shared word producer in definition order. -/
def findRepresentative? (p : Program inputs sigs [word]) : Option (EntryAdd p) :=
  (wordProducers p.diamond.shared).find? (check p)

/-- Inspect the actual right-materialized suffix and forward the selected
entry add through the existing typed emitter. -/
def discoverAndRewrite? (p : Program inputs sigs [word]) : Option (Program inputs sigs [word, word]) := do
  let value ← rightValue? p.suffix
  let rep ← findRepresentative? p
  pure (emit p rep value.val)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative
