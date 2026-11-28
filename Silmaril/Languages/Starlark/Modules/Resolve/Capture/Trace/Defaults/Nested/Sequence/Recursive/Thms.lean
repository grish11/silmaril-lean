module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Execution

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open Assignment (LexicalBlock)
open Functions
open Lists (State Capture Outcome)
open Lists.Iteration (Flow finishState)

theorem default_layout {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) (named : KeywordLexical parent keywords) :
    site.declaration.signature.defaulted.map Prod.fst = site.defaultKeys ∧
      site.declaration.signature.defaulted.map Prod.snd = site.defaultsInOrder.map PlainPositionalDefault.value :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.default_layout
    site named

theorem site_slots {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) :
    site.declaration.signature.slots ++ site.declaration.locals = site.block.owned.map fileSlot :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.site_slots
    site

theorem compile_site {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) (named : KeywordLexical parent keywords)
    {seed middle : Program} (compiled : compileBody ⟨site.block.context, .local⟩ site.source seed =
      .ok (site.body, middle)) :
    compileBody ⟨parent.context, .local⟩ site.statement seed =
      .ok (⟨.define (fileSlot site.name) middle.size, site.reads⟩, middle.push site.declaration) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.compile_site
    site named compiled

theorem lexical_defaults {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) (named : KeywordLexical parent keywords) :
    Lexical.Elaborates parent site.defaultSources site.defaultsInOrder :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.lexical_defaults
    site named

/-- Independent recursive elaboration agrees with the normalized compiler. -/
theorem compiles {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (resolved, final) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.compiles profile

theorem collects {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∃ occurrences, Block.BodyBinders source occurrences :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.collects profile

theorem read_origins {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∀ binding ∈ resolved.reads, ∃ origin, ReadOrigin block binding origin :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.read_origins profile

/-- Reads from nested definitions contribute to the enclosing free
references through their ordered demands, even without a direct read. -/
theorem selects {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∃ free, Selects block resolved.reads free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.selects profile

/-- Every emission has the same lookup after any later sibling or
enclosing definition has been appended. The incoming table is preserved. -/
theorem links {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    PreservesDeclarations seed final ∧ ∀ entry ∈ emissions, final[entry.1]? = some entry.2 :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.links profile

theorem indices {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    emissions.map Prod.fst = List.range' seed.size emissions.length ∧ final.size = seed.size + emissions.length :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.indices profile

/-- A child's free reference needs forwarding exactly when it is
global or the parent does not own that local name. -/
theorem forwarding_request {parent : LexicalBlock} (site : Site parent)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    (binding : Binding) (present : (⟨binding, binding⟩ : FreeName) ∈ site.free) :
    (⟨binding, binding⟩ : FreeName) ∈ free ↔ binding.scope = .global ∨ binding.name ∉ parent.owned :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.forwarding_request
    site selected binding present

theorem installs {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent keywords varargs kwargs)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    {state : State} {floor : Nat} (frame : Body.Frame parent free floor state) :
    ∃ captures, Installs state site.free captures ∧ Body.CaptureCells state captures :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.installs site selected frame

/-- Along a forwarded edge the child's activation keeps the exact address
supplied by the defining frame. An owning frame can instead supply its
shadowing cell. This is independent of the size of the child's body. -/
theorem activate_address {parent : LexicalBlock} (site : Site parent)
    {defining : State} {captures : List Capture} (installed : Installs defining site.free captures)
    (caller : State) (assigned : List (Binding × Lists.Value))
    (binding : Binding) (address : Nat) (present : (⟨binding, binding⟩ : FreeName) ∈ site.free)
    (origin : Forwarding.HasAddress defining binding address) :
    (activate caller site.declaration captures assigned).slots binding =
      some (.captured address (binding.scope == .local)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.activate_address
    site installed caller assigned binding address present origin

/-- Reaching a recursively elaborated definition still uses the same
lexical defaults and capture installation rule. The child body only
runs when its closure is invoked. -/
theorem reached {parent : LexicalBlock} (site : Site parent)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    (program : Program) (available : List DeclarationId) (id : DeclarationId)
    (found : program[id]? = some site.declaration) {state : State} {floor : Nat}
    (frame : Body.Frame parent free floor state) :
    ∃ captures out, Installs state site.free captures ∧ Body.CaptureCells state captures ∧
      Lexical.Defines parent (fileSlot site.name) id site.free site.parameters site.defaults state out ∧
      Exec program available state (.define (fileSlot site.name) id) out ∧
      denoteBody program available (.define (fileSlot site.name) id) state = out ∧
      (∀ next, out = .ok .next next → ∃ evaluated values,
        Lexical.Evaluates parent state site.defaults (.ok values evaluated) ∧
        next = install (fileSlot site.name) id captures
          ((site.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values) evaluated) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.reached
    site selected program available id found frame

/-- Execute the full recursive suite from its reached frame. Definitions
use the appended declaration at each site and leave their child bodies
for invocation. The first error stops the tail with the exact heap. -/
theorem runs {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) (program : Program)
    (linked : PreservesDeclarations final program) (available : List DeclarationId)
    {before after : List Binding} {free : List FreeName} (selection : Selects block (before ++ resolved.reads ++ after) free)
    (state : State) {floor : Nat} (frame : Body.Frame block free floor state) :
    ∃ out, Runs block state source resolved.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec program available state resolved.code out ∧
      denoteBody program available resolved.code state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.runs
    profile program linked available selection state frame

/-- Activate the actual declaration from bound arguments and live captured
cells. The independent suite trace and denotation agree before caller
restoration. The returned or failed observation retains caller cells. -/
theorem runs_activated {parent : LexicalBlock} (site : Site parent) {seed final : Program}
    {emissions : Emissions} (profile : Elaborates site.block site.source seed site.body final emissions)
    (program : Program) (linked : PreservesDeclarations final program) (available : List DeclarationId)
    (caller defining : State) (captures : List Capture) (installed : Installs defining site.free captures)
    (cells : Body.CaptureCells caller captures) (assigned : List (Binding × Lists.Value)) :
    let active := activate caller site.declaration captures assigned
    ∃ out, Runs site.block active site.source site.body.code out ∧
      Body.Frame site.block site.free caller.heap.size (finishState out) ∧
      Exec program available active site.body.code out ∧ denoteBody program available site.body.code active = out ∧
      (let returned := finishState (Leaf.returnTo caller out)
       returned.slots = caller.slots ∧ returned.bindings = caller.bindings ∧
        ∀ (address : Nat) (cell : Lists.Cell), caller.heap[address]? = some cell → returned.heap[address]? = some cell) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.runs_activated
    site profile program linked available caller defining captures installed cells assigned

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
