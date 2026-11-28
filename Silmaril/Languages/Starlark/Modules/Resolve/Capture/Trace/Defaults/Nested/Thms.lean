module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Reached

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested

open Assignment (LexicalBlock)
open Functions
open Lists (State Capture)

local notation "Source" => Body.Definition

/-- Independent binder and operand derivations determine the ordered
child layout and free references. -/
theorem plan_of_body {parent : LexicalBlock} {source : Source} (target : source.name ∈ parent.owned)
    {locals : List String} (binders : Block.LocalBinders source.parameters.names source.body.binders locals)
    {code : Functions.Body} {reads : List Binding}
    (body : Body.Elaborates ⟨source.parameters.names ++ locals, parent.owned ++ parent.enclosing,
      parent.globals⟩ source.body code reads)
    {items : List PlainPositionalDefault} (defaults : Lexical.Elaborates parent source.parameters.optional items) :
    Nonempty (Plan parent source) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.plan_of_body target binders body defaults

/-- The child is emitted at the next code-table index. Its defining
block receives both categories of read demands in source order. -/
theorem compile_definition {parent : LexicalBlock} {source : Source} (plan : Plan parent source) (seed : Program) :
    compileBody ⟨parent.context, .local⟩ (statement source) seed =
      .ok (⟨.define (fileSlot source.name) seed.size, plan.reads⟩, seed.push plan.declaration) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.compile_definition plan seed

/-- Child capture demands are resolved in the parent before deciding
which bindings terminate there and which are inherited. -/
theorem definition_read_origins {parent : LexicalBlock} {owned : List String}
    {bodyReads : List Binding} {free : List FreeName}
    (child : Selects ⟨owned, parent.owned ++ parent.enclosing, parent.globals⟩ bodyReads free)
    {optionals : List (String × Lowering.Resolve.SourceExpr)} {items : List PlainPositionalDefault}
    (lexical : Lexical.Elaborates parent optionals items) :
    ∀ binding ∈ items.flatMap PlainPositionalDefault.reads ++ free.map FreeName.source,
      ∃ origin, ReadOrigin parent binding origin :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.definition_read_origins child lexical

theorem read_origins {parent : LexicalBlock} {source : Source} (plan : Plan parent source) :
    ∀ binding ∈ plan.reads, ∃ origin, ReadOrigin parent binding origin :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.read_origins plan

/-- The child's definition-site demands can be inserted among the
parent's other reads to derive the parent's own ordered capture list. -/
theorem selects_parent {parent : LexicalBlock} {source : Source} (plan : Plan parent source)
    {before after : List Binding}
    (surrounding : ∀ binding ∈ before ++ after, ∃ origin, ReadOrigin parent binding origin) :
    ∃ free, Selects parent (before ++ plan.reads ++ after) free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.selects_parent plan surrounding

theorem installs_from_frame {parent : LexicalBlock} {owned : List String}
    {bodyReads parentReads : List Binding} {childFree parentFree : List FreeName}
    (child : Selects ⟨owned, parent.owned ++ parent.enclosing, parent.globals⟩ bodyReads childFree)
    (selected : Selects parent parentReads parentFree)
    (requested : ∀ entry ∈ childFree, entry.source ∈ parentReads)
    {state : State} {floor : Nat} (frame : Body.Frame parent parentFree floor state) :
    ∃ captures, Installs state childFree captures ∧ Body.CaptureCells state captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.installs_from_frame child selected requested frame

/-- Activation uses the original cell, whether owned or inherited by the defining frame. -/
theorem activate_address {block : LexicalBlock} {reads : List Binding} {declaration : Declaration}
    (selected : Selects block reads declaration.free)
    (slots : declaration.signature.slots ++ declaration.locals = block.owned.map fileSlot)
    {defining : State} {captures : List Lists.Capture} (installed : Installs defining declaration.free captures)
    (caller : State) (assigned : List (Binding × Lists.Value))
    (binding : Binding) (address : Nat) (present : (⟨binding, binding⟩ : FreeName) ∈ declaration.free)
    (origin : Forwarding.HasAddress defining binding address) :
    (activate caller declaration captures assigned).slots binding = some (.captured address (binding.scope == .local)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.activate_address
    selected slots installed caller assigned binding address present origin

/-- Select the child's captures from the reached parent frame. A local
declared in the parent supplies its owned address. Other requests use
the inherited slot, retaining its address and local or module tag. -/
theorem installs {parent : LexicalBlock} {source : Source} (plan : Plan parent source)
    {before after : List Binding} {parentFree : List FreeName}
    (selected : Selects parent (before ++ plan.reads ++ after) parentFree)
    {state : State} {floor : Nat} (frame : Body.Frame parent parentFree floor state) :
    ∃ captures, Installs state plan.body.free captures ∧ Body.CaptureCells state captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.installs plan selected frame

/-- When the parent already forwarded a local, activating the child
with the derived vector keeps that same address across caller changes. -/
theorem activate_forwarded {parent : LexicalBlock} {source : Source} (plan : Plan parent source)
    {state : State} {captures : List Lists.Capture} (installed : Installs state plan.body.free captures)
    (caller : State) (assigned : List (Binding × Lists.Value)) (name : String) (address : Nat)
    (present : (⟨fileSlot name, fileSlot name⟩ : FreeName) ∈ plan.body.free)
    (forwarded : state.slots (fileSlot name) = some (.captured address true)) :
    (activate caller plan.declaration captures assigned).slots (fileSlot name) = some (.captured address true) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.activate_forwarded plan installed
    caller assigned name address present forwarded

theorem reached_site_for {parent : LexicalBlock} {name : String} {keys : List Binding} {expressions : List (String × Lowering.Resolve.SourceExpr)}
    {items : List PlainPositionalDefault} (target : name ∈ parent.owned)
    (lexical : Lexical.Elaborates parent expressions items)
    (program : Program) (available : List DeclarationId) (id : DeclarationId)
    (declaration : Declaration) (found : program[id]? = some declaration)
    (defaultKeys : declaration.signature.defaulted.map Prod.fst = keys)
    (codes : declaration.signature.defaulted.map Prod.snd = items.map PlainPositionalDefault.value)
    {state : State} {free : List FreeName} {floor : Nat} (frame : Body.Frame parent free floor state)
    (captures : List Capture) (supplied : Installs state declaration.free captures) :
    ∃ out, Lexical.DefinesFor parent (fileSlot name) id declaration.free keys items state out ∧
      Exec program available state (.define (fileSlot name) id) out ∧
      denoteBody program available (.define (fileSlot name) id) state = out ∧
      SiteResultFor parent name keys items id captures state out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.reached_site_for
    target lexical program available id declaration found defaultKeys codes frame captures supplied

theorem site_result_frame_for {parent : LexicalBlock} {name : String} {keys : List Binding} {expressions : List (String × Lowering.Resolve.SourceExpr)}
    {items : List PlainPositionalDefault} (target : name ∈ parent.owned)
    (lexical : Lexical.Elaborates parent expressions items) {id : DeclarationId} {captures : List Capture}
    {state : State} {free : List FreeName} {floor : Nat} (frame : Body.Frame parent free floor state)
    {out : Lists.Outcome Lists.Iteration.Flow} (result : SiteResultFor parent name keys items id captures state out) :
    Body.Frame parent free floor (Lists.Iteration.finishState out) ∧
      Body.Keeps floor state (Lists.Iteration.finishState out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.site_result_frame_for
    target lexical frame result

theorem reached_site {parent : LexicalBlock} {name : String} {parameters : Parameters}
    {items : List PlainPositionalDefault} (target : name ∈ parent.owned)
    (lexical : Lexical.Elaborates parent parameters.optional items)
    (program : Program) (available : List DeclarationId) (id : DeclarationId)
    (declaration : Declaration) (found : program[id]? = some declaration)
    (signature : declaration.signature = parameters.signature (items.map PlainPositionalDefault.value))
    {state : State} {free : List FreeName} {floor : Nat} (frame : Body.Frame parent free floor state)
    (captures : List Lists.Capture) (supplied : Installs state declaration.free captures) :
    ∃ out, Lexical.Defines parent (fileSlot name) id declaration.free parameters items state out ∧
      Exec program available state (.define (fileSlot name) id) out ∧
      denoteBody program available (.define (fileSlot name) id) state = out ∧
      SiteResult parent name parameters items id captures state out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.reached_site
    target lexical program available id declaration found signature frame captures supplied

theorem site_result_frame {parent : LexicalBlock} {name : String} {parameters : Parameters}
    {items : List PlainPositionalDefault} (target : name ∈ parent.owned)
    (lexical : Lexical.Elaborates parent parameters.optional items)
    {id : DeclarationId} {captures : List Lists.Capture} {state : State} {free : List FreeName} {floor : Nat}
    (frame : Body.Frame parent free floor state) {out : Lists.Outcome Lists.Iteration.Flow}
    (result : SiteResult parent name parameters items id captures state out) :
    Body.Frame parent free floor (Lists.Iteration.finishState out) ∧
      Body.Keeps floor state (Lists.Iteration.finishState out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.site_result_frame target lexical frame result

/-- A definition preserves the owned and inherited slot layout on
either exit. Successful installation only writes the owned target. -/
theorem result_frame {parent : LexicalBlock} {source : Source} (plan : Plan parent source)
    {id : DeclarationId} {captures : List Lists.Capture} {state : State} {free : List FreeName} {floor : Nat}
    (frame : Body.Frame parent free floor state) {out : Lists.Outcome Lists.Iteration.Flow}
    (result : DefinitionResult plan id captures state out) :
    Body.Frame parent free floor (Lists.Iteration.finishState out) ∧
      Body.Keeps floor state (Lists.Iteration.finishState out) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.result_frame plan frame result

/-- At a reached nested definition, the compiled declaration, full
parent selection, and frame invariant suffice to derive the capture
vector and the independent definition step. -/
theorem reached {parent : LexicalBlock} {source : Source} (plan : Plan parent source)
    {before after : List Binding} {parentFree : List FreeName}
    (selected : Selects parent (before ++ plan.reads ++ after) parentFree)
    (program : Program) (available : List DeclarationId) (id : DeclarationId)
    (found : program[id]? = some plan.declaration) {state : State} {floor : Nat}
    (frame : Body.Frame parent parentFree floor state) :
    ∃ captures out, Installs state plan.body.free captures ∧ Body.CaptureCells state captures ∧
      Lexical.Defines parent (fileSlot source.name) id plan.body.free source.parameters plan.defaults state out ∧
      Exec program available state (.define (fileSlot source.name) id) out ∧
      denoteBody program available (.define (fileSlot source.name) id) state = out ∧
      DefinitionResult plan id captures state out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.reached plan selected
    program available id found frame

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested
