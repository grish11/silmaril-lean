module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open Assignment (LexicalBlock)
open Functions (Declaration DeclarationId Program)

local notation "Expr" => Functions.Lowering.Resolve.SourceExpr

/-- The resolved frame places the collectors after the ordinary slots,
with the positional collector first. The collectors contribute no defaults. -/
@[expose] def parameterNames (positionals : Parameters) (keywords : List PlainKeywordParameter)
    (varargs kwargs : Option String) : List String :=
  let named := match keywords with
    | [] => positionals.names
    | first :: rest => positionals.names ++ (first :: rest).map (SourceParameter.name ∘ PlainKeywordParameter.source)
  let withPositional := match varargs with
    | none => named
    | some name => named ++ [name]
  match kwargs with
  | none => withPositional
  | some name => withPositional ++ [name]

@[expose] def keywordDefaults (keywords : List PlainKeywordParameter) : List PlainPositionalDefault :=
  keywords.filterMap PlainKeywordParameter.default

abbrev KeywordLexical (block : LexicalBlock) (keywords : List PlainKeywordParameter) : Prop :=
  Lexical.Elaborates block ((keywordDefaults keywords).map fun item => (item.name, item.source))
    (keywordDefaults keywords)

/-- The evidence for a single definition site, including the child's
whole-block binder order and the independently selected free references. -/
structure Site (parent : LexicalBlock) (keywords : List PlainKeywordParameter := [])
    (varargs : Option String := none) (kwargs : Option String := none) (scope : Scope := .local) where
  name : String
  target : name ∈ (match scope with | .local => parent.owned | .global => parent.globals)
  parameters : Parameters
  source : Statement
  binders : List String
  locals : List String
  collects : Block.BodyBinders source binders
  localOrder : Block.LocalBinders (parameterNames parameters keywords varargs kwargs) binders locals
  body : ResolvedBody
  free : List Functions.FreeName
  selects : Selects ⟨parameterNames parameters keywords varargs kwargs ++ locals, parent.owned ++ parent.enclosing, parent.globals⟩ body.reads free
  defaults : List PlainPositionalDefault
  lexical : Lexical.Elaborates parent parameters.optional defaults

@[expose] def Site.block {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) : LexicalBlock :=
  ⟨parameterNames site.parameters keywords varargs kwargs ++ site.locals, parent.owned ++ parent.enclosing, parent.globals⟩

@[expose] def Site.sourceSignature {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) : SourceSignature :=
  { site.parameters.source with keywordOnly := keywords.map PlainKeywordParameter.source, varargs := varargs, kwargs := kwargs }

@[expose] def Site.statement {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) : Statement :=
  .define site.name site.sourceSignature site.source

@[expose] def Site.declaration {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) : Declaration :=
  let signature := site.parameters.signature (site.defaults.map PlainPositionalDefault.value)
  ⟨{ signature with
      keywordOnly := keywords.map PlainKeywordParameter.resolved
      varargs := varargs.map fileSlot
      kwargs := kwargs.map fileSlot },
    site.locals.map fileSlot, site.free, site.body.code⟩

@[expose] def Site.defaultSources {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) : List (String × Expr) :=
  match keywords with
  | [] => site.parameters.optional
  | first :: rest => site.parameters.optional ++ (keywordDefaults (first :: rest)).map (fun item => (item.name, item.source))

@[expose] def Site.defaultKeys {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) : List Binding :=
  site.defaultSources.map (fileSlot ∘ Prod.fst)

@[expose] def Site.defaultsInOrder {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) : List PlainPositionalDefault :=
  match keywords with
  | [] => site.defaults
  | first :: rest => site.defaults ++ keywordDefaults (first :: rest)

/-- The parent reads defaults at the definition site and supplies the
body's capture demands in first-occurrence order. -/
@[expose] def Site.reads {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) : List Binding :=
  site.defaultsInOrder.flatMap PlainPositionalDefault.reads ++ site.free.map Functions.FreeName.source

abbrev Emissions := List (DeclarationId × Declaration)

/-- Finite derivations descend into both the child suite and the tail.
The child suite emits its descendants first. The parent declaration
then precedes all declarations in the tail of the defining suite. -/
inductive Elaborates : LexicalBlock → Statement → Program → ResolvedBody → Program → Emissions → Prop where
  | straight {block : LexicalBlock} {source : Body.Suite} {code : Functions.Body} {reads : List Binding} {seed : Program} :
      Body.Elaborates block source code reads →
      Elaborates block source.source seed ⟨code, reads⟩ seed []
  | define {parent : LexicalBlock} {leading : List (String × Expr)}
      {leadingCode : List (String × Functions.Lowering.Expr)} {leadingReads : List Binding}
      {rest : Statement} {seed childTable final : Program} {tail : ResolvedBody}
      {descendants remaining : Emissions} (site : Site parent) :
      Body.ElaboratesPrefix parent leading leadingCode leadingReads →
      Elaborates site.block site.source seed site.body childTable descendants →
      Elaborates parent rest (childTable.push site.declaration) tail final remaining →
      Elaborates parent (Body.prependSource leading (.seq site.statement rest)) seed
        ⟨Body.prependCode leadingCode (.seq (.define (fileSlot site.name) childTable.size) tail.code),
          leadingReads ++ (site.reads ++ tail.reads)⟩ final
        (descendants ++ (childTable.size, site.declaration) :: remaining)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
