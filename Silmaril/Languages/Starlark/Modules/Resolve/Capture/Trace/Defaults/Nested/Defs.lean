module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested

open Assignment (LexicalBlock)
open Functions (Declaration)

local notation "Source" => Body.Definition

/-- A nested definition binds its name in the immediate parent. Its
defaults read the parent and its straight-line body reads the child block. -/
@[expose] def statement (source : Source) : Statement :=
  .define source.name source.parameters.source source.body.source

structure Plan (parent : LexicalBlock) (source : Source) where
  target : source.name ∈ parent.owned
  body : Body.Plan parent.globals source (parent.owned ++ parent.enclosing)
  defaults : List PlainPositionalDefault
  lexical : Lexical.Elaborates parent source.parameters.optional defaults

@[expose] def Plan.declaration {parent : LexicalBlock} {source : Source}
    (plan : Plan parent source) : Declaration :=
  plan.body.declaration (plan.defaults.map PlainPositionalDefault.value)

/-- The parent needs the default reads in order, followed by the child's
ordered free references. Owned parent names terminate a capture request. -/
@[expose] def Plan.reads {parent : LexicalBlock} {source : Source}
    (plan : Plan parent source) : List Binding :=
  plan.defaults.flatMap PlainPositionalDefault.reads ++ plan.body.free.map Functions.FreeName.source

/-- The child binding and function record use the address allocated
after all defaults. A default error instead leaves the old cells intact. -/
inductive SiteResultFor (parent : LexicalBlock) (name : String) (keys : List Binding)
    (items : List PlainPositionalDefault)
    (id : Functions.DeclarationId) (captures : List Lists.Capture) (state : Lists.State) :
    Lists.Outcome Lists.Iteration.Flow → Prop where
  | installed {saved : List Lists.Value} {next evaluated : Lists.State} :
      Lexical.Evaluates parent state items (.ok saved evaluated) →
      next = install (fileSlot name) id captures
        (keys.zip saved) evaluated →
      next.bindingValue (fileSlot name) = .ok (.function evaluated.heap.size) →
      next.heap[evaluated.heap.size]? = some ⟨.function ⟨id, captures,
        keys.zip saved⟩, false⟩ →
      SiteResultFor parent name keys items id captures state (.ok .next next)
  | failed {error : Lists.Error} {next : Lists.State} :
      Lexical.Evaluates parent state items (.error error next) →
      Body.Keeps state.heap.size state next →
      SiteResultFor parent name keys items id captures state (.error error next)

abbrev SiteResult (parent : LexicalBlock) (name : String) (parameters : Parameters) :=
  SiteResultFor parent name (parameters.optional.map (fileSlot ∘ Prod.fst))

abbrev DefinitionResult {parent : LexicalBlock} {source : Source} (plan : Plan parent source) :=
  SiteResult parent source.name source.parameters plan.defaults

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested
