module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site Emissions)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (resolveTracked)

theorem compiles {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} {returned : Option (Entry block)}
    (profile : Elaborates block locals source seed code final emissions returned) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (code, final) := by
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.compiles ordinary
  | returnLocal owned legal _ =>
    exact Body.compile_suite (.ret (.read legal (.owned owned) (.owned owned))) _
  | assign owned operand _ _ rest =>
    simpa only [List.append_nil, Body.prependSource, Body.prependCode, List.foldr_cons, List.foldr_nil] using
      Body.compile_prefix (.cons owned operand .nil) rest
  | define site kw _ _ child rest =>
    exact compileBody_plainSeq _ _ _ _ _ _ _ _
      (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.compile_site site kw child)
      rest
  | invoke call _ _ _ rest =>
    have called := Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.resolves
      call.calleeLegal call.calleeOwned call.operands call.keywords call.star call.mapping
    exact compileBody_plainSeq _ _ _ _ _ _ _ _ (compileBody_plainAssign _ _ _ _ _ _ called) rest

theorem collects {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} {returned : Option (Entry block)}
    (profile : Elaborates block locals source seed code final emissions returned) :
    ∃ names, Block.BodyBinders source names := by
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.collects ordinary
  | returnLocal _ _ _ => exact ⟨[], .ret _⟩
  | assign _ _ _ _ rest =>
    obtain ⟨_, binders⟩ := rest
    exact ⟨_, .seq (.assign _ _) binders⟩
  | define _ _ _ _ _ rest =>
    obtain ⟨_, binders⟩ := rest
    exact ⟨_, .seq (.define _ _ _) binders⟩
  | invoke call _ _ _ rest =>
    obtain ⟨_, binders⟩ := rest
    exact ⟨_, .seq (.assign _ _) binders⟩

theorem links {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} {returned : Option (Entry block)}
    (profile : Elaborates block locals source seed code final emissions returned) :
    PreservesDeclarations seed final ∧ ∀ entry ∈ emissions, final[entry.1]? = some entry.2 := by
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.links ordinary
  | returnLocal _ _ _ => exact ⟨fun _ _ found => found, fun _ no => nomatch no⟩
  | assign _ _ _ _ rest => exact rest
  | invoke _ _ _ _ rest => exact rest
  | @define block locals rest seed childTable tail final descendants later returned formals varargs kwargs site _ _ _ child tailLinks =>
    have retained : PreservesDeclarations childTable final := by
      intro id entry found
      have below := (Array.getElem?_eq_some_iff.mp found).choose
      exact tailLinks.1 id entry (by simp [Array.getElem?_push, Nat.ne_of_lt below, found])
    refine ⟨fun id entry found => retained id entry (child.1 id entry found), ?_⟩
    intro entry seen
    rcases List.mem_append.mp seen with inner | remaining
    · exact retained _ _ (child.2 entry inner)
    · rcases List.mem_cons.mp remaining with rfl | later
      · exact tailLinks.1 _ _ Array.getElem?_push_size
      · exact tailLinks.2 entry later

private theorem argument_origins {block : LexicalBlock}
    {arguments : List Lowering.Resolve.SourceExpr} {code : List Lowering.Expr} {reads : List Binding}
    (related : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Arguments
      block arguments code reads) : ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin := by
  induction related with
  | nil => simp
  | cons operand _ ih =>
    intro binding member
    exact (List.mem_append.mp member).elim (Body.operand_origins operand binding) (ih binding)

theorem selects {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} {returned : Option (Entry block)}
    (profile : Elaborates block locals source seed code final emissions returned) :
    ∃ free, Selects block code.reads free := by
  apply selects_of_origins
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.read_origins ordinary
  | returnLocal owned _ _ =>
    intro binding member
    have eq := List.mem_singleton.mp member
    subst binding
    exact ⟨.owned, .owned owned⟩
  | assign _ operand _ _ rest =>
    intro binding member
    exact (List.mem_append.mp member).elim (Body.operand_origins operand binding) (rest binding)
  | define site kw _ _ _ rest =>
    intro binding member
    exact (List.mem_append.mp member).elim (Nested.definition_read_origins site.selects
      (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.lexical_defaults site kw)
      binding) (rest binding)
  | invoke call _ _ _ rest =>
    intro binding member
    rcases List.mem_append.mp member with current | later
    · rcases List.mem_cons.mp current with rfl | argument
      · exact ⟨.owned, .owned call.calleeOwned⟩
      · rcases List.mem_append.mp argument with earlier | mapping
        · rcases List.mem_append.mp earlier with explicit | spread
          · exact (List.mem_append.mp explicit).elim (argument_origins call.operands binding)
              (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.argument_origins
                call.keywords.related binding)
          · exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.spread_origins
              call.star binding spread
        · exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.mapping_origins
            call.mapping binding mapping
    · exact rest binding later

/-- The returned declaration is selected by the same source-order provenance
updates as the suite. Its body and declaration remain in the final table. -/
theorem return_link {block : LexicalBlock} {locals : Locals block} {source : Statement}
    {seed final program : Program} {code : ResolvedBody} {emissions : Emissions}
    {returned : Option (Entry block)}
    (profile : Elaborates block locals source seed code final emissions returned)
    (table : PreservesDeclarations final program)
    (known : ∀ name entry, locals name = some entry → entry.Linked program) :
    ∀ entry, returned = some entry → entry.Linked program := by
  induction profile with
  | plain _ => intro _ impossible; cases impossible
  | returnLocal _ _ tracked =>
    intro entry same
    cases same
    exact known _ _ tracked
  | @assign _ _ name _ _ _ _ _ _ _ _ _ _ _ _ tracks _ ih =>
    apply ih table
    intro read entry chosen
    by_cases hit : read = name
    · subst read
      simp [setLocal] at chosen
      cases tracks with
      | forget => cases chosen
      | copy _ original => cases chosen; exact known _ _ original
    · exact known read entry (by simpa [setLocal, hit] using chosen)
  | @define block locals rest seed childTable tail final descendants later returned formals varargs kwargs site _ child suffix _ ih =>
    apply ih table
    intro read entry chosen
    by_cases hit : read = site.name
    · subst read
      simp [setLocal] at chosen
      cases chosen
      have linked : PreservesDeclarations (childTable.push site.declaration) program :=
        fun id decl found => table id decl ((links suffix).1 id decl found)
      refine ⟨linked _ _ Array.getElem?_push_size, _, _, _, rfl, ?_, child⟩
      intro id decl found
      exact linked _ _ (by simp [Array.getElem?_push, Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp found).choose, found])
    · exact known read entry (by simpa [setLocal, hit] using chosen)
  | invoke call _ _ _ ih =>
    apply ih table
    intro read entry chosen
    by_cases hit : read = call.destination
    · simp [setLocal, hit] at chosen
    · exact known read entry (by simpa [setLocal, hit] using chosen)

/-- The full table minus the enclosing definition still contains this suite's emissions. -/
theorem entry_guard {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final program : Program}
    {code : ResolvedBody} {emissions : Emissions} {returned : Option (Entry block)}
    (profile : Elaborates block locals source seed code final emissions returned)
    (table : PreservesDeclarations final program) :
    List.Subset (emissions.map Prod.fst) (withoutDeclaration (List.range program.size) final.size) := by
  intro id member
  obtain ⟨entry, emitted, rfl⟩ := List.mem_map.mp member
  have found := (links profile).2 entry emitted
  exact mem_withoutDeclaration.mpr ⟨List.mem_range.mpr (Array.getElem?_eq_some_iff.mp (table _ _ found)).choose,
    Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp found).choose⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
