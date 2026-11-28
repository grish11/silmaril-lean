module

public import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern.Table
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern

open Silmaril.SSA.SeaOfNodes.Diamond
open Silmaril.SSA.SeaOfNodes.GVN.Elimination (read_splitOrigin splitOrigin)
open Silmaril.SSA.SeaOfNodes.GVN.WordNumber (Key entryKeys keyArguments numbering)
open Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (BinaryOpcode Opcode word wordPort)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {table : Table} {entry : Tuple IdVal args} {locals : Locals IdVal past}
variable {keys : Tuple (Val (numbering args).value) args} {numbered : Locals (Val (numbering args).value) past}

private theorem op_spec (agrees : Agrees table entry locals keys numbered)
    {ins : List (ValueSort Unit)} (op : Opcode ins word) (wires : Wires args past (dataPorts ins)) :
    let result := internOp table op (wires.read entry locals)
    table <+: result.1 ∧ (table.Nodup → result.1.Nodup) ∧
      Decodes result.1 result.2 ((numbering args).run op (wires.read keys numbered)) := by
  have binary (opcode : BinaryOpcode) (lhs rhs : Origin args past wordPort) :
      let result := intern table (.binary opcode (readId entry locals lhs) (readId entry locals rhs))
      table <+: result.1 ∧ (table.Nodup → result.1.Nodup) ∧
        Decodes result.1 result.2 (.binary opcode (read (numbering args) lhs keys numbered)
          (read (numbering args) rhs keys numbered)) :=
    let ⟨extendsTable, found, unique⟩ := intern_spec table _
    ⟨extendsTable, unique, .binary found (decodes_mono extendsTable (agrees lhs)) (decodes_mono extendsTable (agrees rhs))⟩
  cases op with
  | literal value =>
    cases wires
    obtain ⟨extendsTable, found, unique⟩ := intern_spec table (.literal value)
    exact ⟨extendsTable, unique, .literal found⟩
  | add | sub | mul =>
    cases wires with
    | cons lhs tail =>
      cases tail with
      | cons rhs tail =>
        cases tail
        first
        | exact binary .add lhs rhs
        | exact binary .sub lhs rhs
        | exact binary .mul lhs rhs

-- The generic split/read law ignores opcode semantics. An empty signature
-- instantiates it for the ID carrier without assigning operations to IDs.
private abbrev idReader : Model (fun (_ : List (ValueSort Unit)) (_ : ValueSort Unit) => Empty) where
  value _ := Id
  run op _ := nomatch op

private theorem snoc_agrees (agrees : Agrees table entry locals keys numbered)
    {id : Id} {key : Key args} (new : Decodes table id key) :
    Agrees table entry (locals.snoc (.cons id .nil : Tuple IdVal [wordPort])) keys
      (numbered.snoc (.cons key .nil : Tuple (Val (numbering args).value) [wordPort])) := by
  intro wire
  change Decodes table (read idReader wire entry (locals.snoc (.cons id .nil)))
    (read (numbering args) wire keys (numbered.snoc (.cons key .nil)))
  rw [← read_splitOrigin wire idReader, ← read_splitOrigin wire (numbering args)]
  cases splitOrigin [wordPort] wire with
  | inl prior => exact agrees prior
  | inr port =>
    cases port with
    | head => exact new
    | tail impossible => cases impossible

private theorem step_spec (agrees : Agrees table entry locals keys numbered)
    {ins : List (ValueSort Unit)} {out : ValueSort Unit} (op : Opcode ins out)
    (wires : Wires args past (dataPorts ins)) :
    let result := internOp table op (wires.read entry locals)
    table <+: result.1 ∧ (table.Nodup → result.1.Nodup) ∧
      Agrees result.1 entry (locals.snoc (Tuple.cons (F := IdVal) (t := .value out) result.2 .nil)) keys
        (numbered.snoc (Tuple.cons (F := Val (numbering args).value) (t := .value out)
          ((numbering args).run op (wires.read keys numbered)) .nil)) := by
  have step {ins : List (ValueSort Unit)} (op : Opcode ins word) (wires : Wires args past (dataPorts ins)) :
      let result := internOp table op (wires.read entry locals)
      table <+: result.1 ∧ (table.Nodup → result.1.Nodup) ∧
        Agrees result.1 entry (locals.snoc (Tuple.cons (F := IdVal) (t := wordPort) result.2 .nil)) keys
          (numbered.snoc (Tuple.cons (F := Val (numbering args).value) (t := wordPort)
            ((numbering args).run op (wires.read keys numbered)) .nil)) :=
    let ⟨extendsTable, unique, new⟩ := op_spec agrees op wires
    ⟨extendsTable, unique, snoc_agrees (fun wire => decodes_mono extendsTable (agrees wire)) new⟩
  cases op with
  | literal value => exact step (.literal value) wires
  | add => exact step .add wires
  | sub => exact step .sub wires
  | mul => exact step .mul wires

theorem eval_spec (flow : Dataflow Opcode args past sigs) (agrees : Agrees table entry locals keys numbered) :
    let result := eval entry flow table locals
    table <+: result.1 ∧ (table.Nodup → result.1.Nodup) ∧
      Agrees result.1 entry result.2 keys (flow.eval (numbering args) keys numbered) := by
  induction flow generalizing table with
  | nil => exact ⟨List.prefix_rfl, fun unique => unique, agrees⟩
  | cons op wires rest ih =>
    obtain ⟨extendsTable, unique, next⟩ := step_spec agrees op wires
    obtain ⟨extendsAfter, uniqueAfter, final⟩ := ih next
    exact ⟨extendsTable.trans extendsAfter, uniqueAfter ∘ unique, final⟩

private theorem seed_spec (inputs : List (ValueSort Unit)) :
    ∀ (lift : ∀ {sort}, Port (dataPorts inputs) (.value sort) → Port args (.value sort)) (table : Table),
      let result := seed inputs lift table
      table <+: result.1 ∧ (table.Nodup → result.1.Nodup) ∧
        ∀ port : Port (dataPorts inputs) wordPort,
          Decodes result.1 (result.2.get port) ((keyArguments args inputs lift).get port) ∧
            Decodes result.1 (result.2.get port) (.argument (lift port)) := by
  induction inputs with
  | nil => exact fun _ _ => ⟨List.prefix_rfl, fun unique => unique, fun port => nomatch port⟩
  | cons sort tail ih =>
    intro lift table
    let liftTail : ∀ {sort}, Port (dataPorts tail) (.value sort) → Port args (.value sort) :=
      fun port => lift (.tail port)
    cases sort with
    | predicate =>
      obtain ⟨extendsTable, unique, agrees⟩ := ih liftTail table
      refine ⟨extendsTable, unique, ?_⟩
      intro port
      cases port with
      | tail inner => exact agrees inner
    | data singleton =>
      cases singleton
      let result := intern table (.argument (lift .head).index)
      obtain ⟨extendsTable, found, unique⟩ := intern_spec table (.argument (lift .head).index)
      obtain ⟨extendsAfter, uniqueAfter, agrees⟩ := ih liftTail result.1
      refine ⟨extendsTable.trans extendsAfter, uniqueAfter ∘ unique, ?_⟩
      intro port
      cases port with
      | head =>
        have decoded := decodes_mono (args := args) extendsAfter (Decodes.argument found)
        exact ⟨decoded, decoded⟩
      | tail inner => exact agrees inner

theorem entry_spec (inputs : List (ValueSort Unit)) :
    let result := entryIds inputs
    result.1.Nodup ∧ Agrees (past := []) result.1 result.2 PUnit.unit (entryKeys inputs) PUnit.unit := by
  obtain ⟨_, unique, agrees⟩ := seed_spec (args := dataPorts inputs) inputs (fun port => port) []
  refine ⟨unique List.nodup_nil, ?_⟩
  intro wire
  cases wire with
  | arg port => exact (agrees port).1
  | output index _ => exact index.elim0

theorem entry_argument {inputs : List (ValueSort Unit)} (port : Port (dataPorts inputs) wordPort) :
    Decodes (entryIds inputs).1 ((entryIds inputs).2.get port) (.argument port) :=
  ((seed_spec (args := dataPorts inputs) inputs (fun p => p) []).2.2 port).2

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.WordNumber.Intern
