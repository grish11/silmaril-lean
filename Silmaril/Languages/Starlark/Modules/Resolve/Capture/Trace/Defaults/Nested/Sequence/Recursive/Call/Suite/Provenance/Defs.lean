module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Functions
open Lists (State)

local notation "Expr" => Lowering.Resolve.SourceExpr

structure Entry (block : LexicalBlock) where
  id : DeclarationId
  formals : List PlainKeywordParameter
  varargs : Option String
  kwargs : Option String
  site : Site block formals varargs kwargs

abbrev Locals (block : LexicalBlock) := String → Option (Entry block)

@[expose] def empty {block : LexicalBlock} : Locals block := fun _ => none

@[expose] def setLocal {block : LexicalBlock} (locals : Locals block) (name : String)
    (entry : Option (Entry block)) : Locals block :=
  fun read => if read = name then entry else locals read

/-- An ordinary assignment forgets the destination. A checked local
name copy transfers its source's current declaration witness. -/
inductive Tracks {block : LexicalBlock} (locals : Locals block) :
    Expr → Lowering.Expr → Option (Entry block) → Prop where
  | forget {source code} : Tracks locals source code none
  | copy {name : String} {entry : Entry block} :
      name ∈ block.owned → locals name = some entry →
      Tracks locals (.scalar (.read name)) (Leaf.readOperand (fileSlot name)) (some entry)

/-- Every tracked local points to an actual closure record in the reached
heap. The slot and closure address are separate, so copying a value does
not couple the later writes to the two local slots. -/
@[expose] def Live {block : LexicalBlock} (locals : Locals block) (state : State) : Prop :=
  ∀ name entry, locals name = some entry →
    ∃ slot address frozen, state.slots (fileSlot name) = some (.owned slot) ∧
      state.heap[slot]? = some ⟨.binding (some (.function address)), frozen⟩ ∧
      ∃ defining, Nonempty (Call.ClosureAt entry.site entry.id defining state address)

structure Invocation (block : LexicalBlock) where
  callee : String
  calleeOwned : callee ∈ block.owned
  calleeLegal : callee.toList.head? ≠ some '$'
  destination : String
  destinationOwned : destination ∈ block.owned
  arguments : List Expr
  codes : List Lowering.Expr
  argumentReads : List Binding
  operands : Call.Arguments block arguments codes argumentReads
  keywords : Named.Operands block := Named.Operands.empty
  star : Option (Named.Spread block) := none
  mapping : Option (Named.Mapping block) := none

@[expose] def Invocation.source {block : LexicalBlock} (call : Invocation block) : Statement :=
  .assign call.destination (.call (.scalar (.read call.callee)) call.arguments call.keywords.source
    (call.star.map Named.Spread.source) (call.mapping.map Named.Mapping.source))

@[expose] def Invocation.code {block : LexicalBlock} (call : Invocation block) : Functions.Body :=
  .assignExpr (fileSlot call.destination) (Named.expression call.callee call.codes call.keywords.codes
    (call.star.map Named.Spread.code) (call.mapping.map Named.Mapping.code))

@[expose] def Invocation.reads {block : LexicalBlock} (call : Invocation block) : List Binding :=
  fileSlot call.callee :: ((call.argumentReads ++ call.keywords.reads) ++ Named.spreadReads call.star ++ Named.mappingReads call.mapping)

/-- Each child starts with an empty provenance map. Only reaching a
local definition or copying a tracked local establishes a known callee. -/
inductive Elaborates : (block : LexicalBlock) → Locals block →
    Statement → Program → ResolvedBody → Program → Emissions → Prop where
  | plain {block locals source seed code final emissions} :
      Recursive.Elaborates block source seed code final emissions →
      Elaborates block locals source seed code final emissions
  | assign {block locals name source rhs reads entry rest seed tail final emissions} :
      name ∈ block.owned → Body.Operand block source rhs reads → Tracks locals source rhs entry →
      Elaborates block (setLocal locals name entry) rest seed tail final emissions →
      Elaborates block locals (.seq (.assign name source) rest) seed
        ⟨.seq (.assignExpr (fileSlot name) rhs) tail.code, reads ++ tail.reads⟩ final emissions
  | define {block locals rest seed childTable tail final descendants later}
      {formals : List PlainKeywordParameter} {varargs kwargs : Option String} (site : Site block formals varargs kwargs) :
      KeywordLexical block formals →
      Elaborates site.block empty site.source seed site.body childTable descendants →
      Elaborates block (setLocal locals site.name (some ⟨childTable.size, formals, varargs, kwargs, site⟩))
        rest (childTable.push site.declaration) tail final later →
      Elaborates block locals (.seq site.statement rest) seed
        ⟨.seq (.define (fileSlot site.name) childTable.size) tail.code, site.reads ++ tail.reads⟩ final
        (descendants ++ (childTable.size, site.declaration) :: later)
  | invoke {block locals rest seed tail final emissions} (call : Invocation block) (entry : Entry block) :
      locals call.callee = some entry →
      Elaborates block (setLocal locals call.destination none) rest seed tail final emissions →
      Elaborates block locals (.seq call.source rest) seed
        ⟨.seq call.code tail.code, call.reads ++ tail.reads⟩ final emissions

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
