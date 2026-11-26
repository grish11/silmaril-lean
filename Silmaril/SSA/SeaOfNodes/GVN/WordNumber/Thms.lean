module

public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.WordNumber

open Diamond (Dataflow Ty Val ValueSort dataPorts read)
open Pure.SubZero (Opcode model wordPort)
open RVSDG (Locals Origin Tuple extend)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}

/-- Matching value numbers have the same argument, literal or ordered
producer tree. The check uses no runtime valuation. -/
theorem Key.eq_of_matches {lhs rhs : Key args} (matched : lhs.matches rhs = true) : lhs = rhs :=
  Proofs.SSA.SeaOfNodes.GVN.WordNumber.matches_eq matched

/-- Native evaluation by structural keys respects all word reads, including
when extending a previously numbered prefix. -/
theorem eval_agrees (flow : Dataflow Opcode args past sigs)
    {entry : Tuple (Val model.value) args} {keys : Tuple (Val (numbering args).value) args}
    {locals : Locals (Val model.value) past} {numbered : Locals (Val (numbering args).value) past}
    (agrees : ∀ wire : Origin args past wordPort,
      (read (numbering args) wire keys numbered).eval entry = read model wire entry locals) :
    ∀ wire : Origin args (extend past sigs) wordPort,
      (read (numbering args) wire keys (flow.eval (numbering args) keys numbered)).eval entry =
        read model wire entry (flow.eval model entry locals) :=
  Proofs.SSA.SeaOfNodes.GVN.WordNumber.eval_agrees flow agrees

/-- A numbered entry reads the corresponding typed word for any input valuation. -/
theorem entry_read_agrees {inputs : List (ValueSort Unit)}
    (entry : Tuple (Val model.value) (dataPorts inputs)) (wire : Origin (dataPorts inputs) [] wordPort) :
    (read (numbering (dataPorts inputs)) wire (entryKeys inputs) PUnit.unit).eval entry =
      read model wire entry PUnit.unit :=
  Proofs.SSA.SeaOfNodes.GVN.WordNumber.entry_read_agrees entry wire

end Silmaril.SSA.SeaOfNodes.GVN.WordNumber
