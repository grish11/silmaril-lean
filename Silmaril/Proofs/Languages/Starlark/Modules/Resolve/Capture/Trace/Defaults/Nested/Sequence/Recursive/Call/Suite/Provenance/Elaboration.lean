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
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (code, final) := by
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.compiles ordinary
  | assign owned operand _ _ rest =>
    simpa only [List.append_nil, Body.prependSource, Body.prependCode, List.foldr_cons, List.foldr_nil] using
      Body.compile_prefix (.cons owned operand .nil) rest
  | define site kw _ _ child rest =>
    exact compileBody_plainSeq _ _ _ _ _ _ _ _
      (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.compile_site site kw child)
      rest
  | invoke call _ _ _ rest =>
    have called := Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.resolves
      call.calleeLegal call.calleeOwned call.operands call.keywords call.star
    exact compileBody_plainSeq _ _ _ _ _ _ _ _ (compileBody_plainAssign _ _ _ _ _ _ called) rest

theorem collects {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions) :
    ∃ names, Block.BodyBinders source names := by
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.collects ordinary
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
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions) :
    PreservesDeclarations seed final ∧ ∀ entry ∈ emissions, final[entry.1]? = some entry.2 := by
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.links ordinary
  | assign _ _ _ _ rest => exact rest
  | invoke _ _ _ _ rest => exact rest
  | @define block locals rest seed childTable tail final descendants later formals varargs kwargs site _ _ _ child tailLinks =>
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
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions) :
    ∃ free, Selects block code.reads free := by
  apply selects_of_origins
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.read_origins ordinary
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
      · rcases List.mem_append.mp argument with explicit | spread
        · exact (List.mem_append.mp explicit).elim (argument_origins call.operands binding)
            (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.argument_origins call.keywords.related binding)
        · exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.spread_origins call.star binding spread
    · exact rest binding later

/-- The full table minus the enclosing definition still contains this suite's emissions. -/
theorem entry_guard {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final program : Program}
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block locals source seed code final emissions)
    (table : PreservesDeclarations final program) :
    List.Subset (emissions.map Prod.fst) (withoutDeclaration (List.range program.size) final.size) := by
  intro id member
  obtain ⟨entry, emitted, rfl⟩ := List.mem_map.mp member
  have found := (links profile).2 entry emitted
  exact mem_withoutDeclaration.mpr ⟨List.mem_range.mpr (Array.getElem?_eq_some_iff.mp (table _ _ found)).choose,
    Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp found).choose⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
