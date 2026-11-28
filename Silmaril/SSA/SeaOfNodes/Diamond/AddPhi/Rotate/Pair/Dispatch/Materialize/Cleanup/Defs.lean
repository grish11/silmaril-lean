module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Defs

/-! Erase the inner right-zero add after materializing its original Φ operand. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup

open Pure.ConstantFold
open Pure.SubZero (word)
open GVN.Elimination (Rewrite)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

abbrev Suffix := Pure.Program Pure.SubZero.Opcode [word, word] word

/-- Read the actual emitted table and return its inner producer. The inner
RHS is the literal, and the returned outer add uses the inner result
followed by the surviving join word. -/
def innerZero? : (p : Suffix) →
    Option {_candidate : GVN.Producer p.dataflow word // p = suffix .left 0}
  | ⟨.cons (.literal value) .nil
      (.cons .add (.cons (.arg .head) (.cons (.output ⟨0, _⟩ .head) .nil))
        (.cons .add (.cons (.output ⟨1, _⟩ .head) (.cons (.arg (.tail .head)) .nil)) .nil)),
      .output ⟨2, _⟩ .head⟩ =>
    if h : value = 0 then some ⟨.later .here, by subst value; rfl⟩ else none
  | _ => none

/-- The expected suffix after the erasure. The now-unused literal is retained. -/
def cleanedSuffix : Suffix where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) .nil)
  result := .output (1 : Fin 2) .head

/-- Nominate the inner add with no source IDs and admit only the
source-ordered right-zero branch. The rewrite retains its typed read map. -/
def suffixEdit? (p : Suffix) : Option (Rewrite Pure.SubZero.Opcode (dataPorts [word, word]) [] p.sigs) := do
  let inner ← innerZero? p
  match AddIdealize.step ⟨fun _ => none⟩ p inner.val with
  | .ok (some ⟨.rightZero, edit⟩) => some edit
  | _ => none

/-- Apply one checked edit to the suffix of the actual materialized
program. Retain the capture and the entire occurrence-indexed diamond. -/
def rewrite? : Result inputs sigs → Option (Program inputs sigs [word])
  | .materialized .left _ p =>
    (suffixEdit? p.suffix).map fun edit =>
      { p with suffix := AddRewrite.rewrittenProgram p.suffix edit }
  | _ => none

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup
