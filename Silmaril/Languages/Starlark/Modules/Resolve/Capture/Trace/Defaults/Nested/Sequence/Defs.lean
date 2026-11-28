module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence

open Assignment (LexicalBlock)
open Functions (DeclarationId Program)
open Lists (Outcome State)
open Lists.Iteration (Flow)

local notation "Expr" => Functions.Lowering.Resolve.SourceExpr
local notation "Code" => Functions.Body

/-- A straight-line suite can contain any finite number of local
definitions. Each definition appends its child before elaborating the
rest of the enclosing suite. The child uses the existing body profile. -/
inductive Elaborates (block : LexicalBlock) : Statement → Program → ResolvedBody → Program → Prop where
  | straight {source : Body.Suite} {code : Code} {reads : List Binding} {seed : Program} :
      Body.Elaborates block source code reads →
      Elaborates block source.source seed ⟨code, reads⟩ seed
  | define {leading : List (String × Expr)} {leadingCode : List (String × Functions.Lowering.Expr)}
      {leadingReads : List Binding} {child : Body.Definition} {rest : Statement}
      {seed final : Program} {tail : ResolvedBody} :
      Body.ElaboratesPrefix block leading leadingCode leadingReads →
      (plan : Nested.Plan block child) →
      Elaborates block rest (seed.push plan.declaration) tail final →
      Elaborates block (Body.prependSource leading (.seq (Nested.statement child) rest)) seed
        ⟨Body.prependCode leadingCode (.seq (.define (fileSlot child.name) seed.size) tail.code),
          leadingReads ++ (plan.reads ++ tail.reads)⟩ final

/-- Later compilation can append declarations without changing any
previously emitted declaration ID. -/
@[expose] def PreservesDeclarations (earlier later : Program) : Prop :=
  ∀ (id : DeclarationId) (declaration : Functions.Declaration), earlier[id]? = some declaration → later[id]? = some declaration

/-- A successful definition gives the tail the reached binding and heap.
Either error rule ends the sequence at that state. -/
inductive Runs (block : LexicalBlock) : State → Statement → Code → Outcome Flow → Prop where
  | straight {source : Body.Suite} {code : Code} {state : State} {out : Outcome Flow} :
      Body.Runs block state source code out → Runs block state source.source code out
  | prefixError {leading : List (String × Expr)} {leadingCode : List (String × Functions.Lowering.Expr)}
      {name : String} {parameters : Parameters} {child rest : Statement} {tail : Code} {id : DeclarationId}
      {state final : State} {error : Lists.Error} :
      Body.RunsPrefix block state leading leadingCode (.error error final) →
      Runs block state (Body.prependSource leading (.seq (.define name parameters.source child) rest))
        (Body.prependCode leadingCode (.seq (.define (fileSlot name) id) tail)) (.error error final)
  | definitionError {leading : List (String × Expr)} {leadingCode : List (String × Functions.Lowering.Expr)}
      {name : String} {parameters : Parameters} {child rest : Statement} {tail : Code} {id : DeclarationId}
      {state active final : State} {error : Lists.Error} {captures : List Lists.Capture}
      {items : List PlainPositionalDefault} :
      Body.RunsPrefix block state leading leadingCode (.ok () active) →
      Nested.SiteResult block name parameters items id captures active (.error error final) →
      Runs block state (Body.prependSource leading (.seq (.define name parameters.source child) rest))
        (Body.prependCode leadingCode (.seq (.define (fileSlot name) id) tail)) (.error error final)
  | define {leading : List (String × Expr)} {leadingCode : List (String × Functions.Lowering.Expr)}
      {name : String} {parameters : Parameters} {child rest : Statement} {tail : Code} {id : DeclarationId}
      {childFree : List Functions.FreeName} {state active installed : State} {captures : List Lists.Capture} {out : Outcome Flow}
      {items : List PlainPositionalDefault} :
      Body.RunsPrefix block state leading leadingCode (.ok () active) →
      Installs active childFree captures →
      Nested.SiteResult block name parameters items id captures active (.ok .next installed) →
      Runs block installed rest tail out →
      Runs block state (Body.prependSource leading (.seq (.define name parameters.source child) rest))
        (Body.prependCode leadingCode (.seq (.define (fileSlot name) id) tail)) out

/-- The reached definition certifies both the local binding and the
function record. A later operand may use this record at the same address. -/
structure Installed {block : LexicalBlock} {child : Body.Definition}
    (plan : Nested.Plan block child) (id : DeclarationId) (captures : List Lists.Capture)
    (state : State) where
  address : Nat
  values : List Lists.Value
  length : values.length = child.parameters.optional.length
  bound : state.bindingValue (fileSlot child.name) = .ok (.function address)
  recorded : state.heap[address]? = some ⟨.function ⟨id, captures,
    (child.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values⟩, false⟩

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence
