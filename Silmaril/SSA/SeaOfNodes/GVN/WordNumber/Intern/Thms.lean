module

public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.Table
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern

open Diamond (Dataflow Ty Val ValueSort dataPorts)
open Pure.SubZero (Opcode wordPort)
open RVSDG (Locals Port Tuple)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {table after : Table}

theorem intern_spec (table : Table) (signature : Signature) :
    let result := intern table signature
    table <+: result.1 ∧ result.1[result.2]? = some signature ∧
      (table.Nodup → result.1.Nodup) :=
  Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.intern_spec table signature

/-- Appending signatures preserves all earlier ID interpretations. -/
theorem Decodes.mono {id : Id} {key : Key args} (decoded : Decodes table id key)
    (extendsTable : table <+: after) : Decodes after id key :=
  Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.decodes_mono extendsTable decoded

/-- In a single duplicate-free table, IDs are equal exactly when their
decoded structural word keys are equal. -/
theorem Decodes.id_eq_iff (unique : table.Nodup) {lhs rhs : Id} {leftKey rightKey : Key args}
    (left : Decodes table lhs leftKey) (right : Decodes table rhs rightKey) :
    lhs = rhs ↔ leftKey = rightKey :=
  ⟨fun same => Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.decoded_eq (same ▸ left) right,
    fun same => Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.id_eq unique (same ▸ left) right⟩

/-- Numbering a native suffix preserves its prefix table, uniqueness, and
agreement with structural numbering at each final typed word read. -/
theorem eval_spec (flow : Dataflow Opcode args past sigs)
    {entry : Tuple IdVal args} {locals : Locals IdVal past}
    {keys : Tuple (Val (numbering args).value) args} {numbered : Locals (Val (numbering args).value) past}
    (agrees : Agrees table entry locals keys numbered) :
    let result := eval entry flow table locals
    table <+: result.1 ∧ (table.Nodup → result.1.Nodup) ∧
      Agrees result.1 entry result.2 keys (flow.eval (numbering args) keys numbered) :=
  Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.eval_spec flow agrees

theorem entry_spec (inputs : List (ValueSort Unit)) :
    let result := entryIds inputs
    result.1.Nodup ∧ Agrees (past := []) result.1 result.2 PUnit.unit (entryKeys inputs) PUnit.unit :=
  Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.entry_spec inputs

theorem entry_argument {inputs : List (ValueSort Unit)} (port : Port (dataPorts inputs) wordPort) :
    Decodes (entryIds inputs).1 ((entryIds inputs).2.get port) (.argument port) :=
  Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.entry_argument port

end Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern
