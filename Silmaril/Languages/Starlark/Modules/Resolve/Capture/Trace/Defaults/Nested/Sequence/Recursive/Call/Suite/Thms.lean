module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Execution

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite

open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Functions
open Lists (State Capture)
open Lists.Iteration (finishState)

/-- The source suite relation predicts normalized assembly of the body. -/
theorem compiles {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (resolved, final) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.compiles
    profile

/-- The current block contains the alias and result binders in statement order. -/
theorem collects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    ∃ names, Block.BodyBinders source names :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.collects
    profile

/-- Calls contribute the alias and ordered argument reads to lexical capture selection. -/
theorem selects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    ∃ free, Selects block resolved.reads free :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.selects
    profile

/-- Every emitted declaration has a stable ID in the final table. -/
theorem links {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    PreservesDeclarations seed final ∧ ∀ entry ∈ emitted, final[entry.1]? = some entry.2 :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.links
    profile

/-- Local call IDs refer to actual emissions of the suite. -/
theorem call_ids {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    List.Subset calls (emitted.map Prod.fst) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.call_ids
    profile

/-- A child's local call IDs precede the child's own emitted ID. -/
theorem child_available {block : LexicalBlock} {source : Statement} {seed childTable : Program}
    {code : ResolvedBody} {emitted : Emissions} {childCalls : List DeclarationId}
    (child : Elaborates block source seed code childTable emitted childCalls)
    {available : List DeclarationId} (guarded : List.Subset childCalls available) :
    List.Subset childCalls (withoutDeclaration available childTable.size) :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.child_available
    child guarded

/-- From the reached frame, a local call reads its installed closure and
commits a result only on success. Subsequent statements see the restored
frame. Every error retains its reached state and ends the suite. -/
theorem runs {block : LexicalBlock} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emitted : Emissions} {calls : List DeclarationId}
    (profile : Elaborates block source seed code final emitted calls)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (available : List DeclarationId) (guarded : List.Subset calls available)
    {before after : List Binding} {free : List FreeName} (selected : Selects block (before ++ code.reads ++ after) free)
    (state : State) {floor : Nat} (frame : Body.Frame block free floor state) :
    ∃ out, Runs block state source code.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec resolved.program available state code.code out ∧
      denoteBody resolved.program available code.code state = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.runs
    profile checked table available guarded selected state frame

/-- Activation obtains the suite frame from live captures and bound arguments. -/
theorem runs_activated {parent : LexicalBlock} (site : Site parent) {seed final : Program}
    {emitted : Emissions} {calls : List DeclarationId}
    (profile : Elaborates site.block site.source seed site.body final emitted calls)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (available : List DeclarationId) (guarded : List.Subset calls available)
    (caller defining : State) (captures : List Capture) (installed : Installs defining site.free captures)
    (live : Body.CaptureCells caller captures)
    (assigned : List (Binding × Lists.Value)) :
    let active := activate caller site.declaration captures assigned
    ∃ out, Runs site.block active site.source site.body.code out ∧
      Body.Frame site.block site.free caller.heap.size (finishState out) ∧
      Body.Keeps caller.heap.size active (finishState out) ∧
      Exec resolved.program available active site.body.code out ∧
      denoteBody resolved.program available site.body.code active = out :=
  Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.runs_activated
    site profile checked table available guarded caller defining captures installed live assigned

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite
