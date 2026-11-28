module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site Emissions)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (resolveTracked)

theorem compile_site {block : LexicalBlock} (site : Site block) {seed childTable : Program}
    (compiled : compileBody ⟨site.block.context, .local⟩ site.source seed = .ok (site.body, childTable)) :
    compileBody ⟨block.context, .local⟩ site.statement seed =
      .ok (⟨.define (fileSlot site.name) childTable.size, site.reads⟩, childTable.push site.declaration) := by
  obtain ⟨same, tracked⟩ := Lexical.translates site.lexical
  exact Body.compile_nested_body site.name site.parameters site.collects site.localOrder
    site.body site.selects site.defaults same tracked _ _ compiled

private theorem compile_assignment {block : LexicalBlock} (site : Site block)
    (legal : site.name.toList.head? ≠ some '$') (assignment : Assignment block) {rest : Statement}
    {seed final : Program} {tail : ResolvedBody} (compiled : compileBody ⟨block.context, .local⟩ rest seed = .ok (tail, final)) :
    compileBody ⟨block.context, .local⟩ (assignment.source site.name rest) seed =
      .ok (⟨assignment.code site.name tail.code, assignment.reads site.name ++ tail.reads⟩, final) := by
  have operand : Body.Operand block (.scalar (.read site.name)) (Leaf.readOperand (fileSlot site.name)) [fileSlot site.name] :=
    .read legal (.owned site.target) (.owned site.target)
  have copied : resolveTracked block.context (.scalar (.read site.name)) =
      .ok (Leaf.readOperand (fileSlot site.name), [fileSlot site.name]) := by
    simp [resolveTracked, Body.resolves_at operand [], Except.map]
  have called := Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.resolves assignment.copyLegal assignment.copyOwned assignment.operands
  exact compileBody_plainSeq _ _ _ _ _ _ _ _
    (compileBody_plainAssign _ _ _ _ _ _ copied)
    (compileBody_plainSeq _ _ _ _ _ _ _ _ (compileBody_plainAssign _ _ _ _ _ _ called) compiled)

theorem compiles {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (resolved, final) := by
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.compiles ordinary
  | assignments leading _ rest => exact Body.compile_prefix leading rest
  | define site _ _ child rest =>
    exact compileBody_plainSeq _ _ _ _ _ _ _ _ (compile_site site child) rest
  | call site legal assignment _ _ child rest =>
    exact compileBody_plainSeq _ _ _ _ _ _ _ _ (compile_site site child)
      (compile_assignment site legal assignment rest)

theorem collects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    ∃ names, Block.BodyBinders source names := by
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.collects ordinary
  | assignments _ _ rest =>
    obtain ⟨_, binders⟩ := rest
    exact ⟨_, Body.collects_prefix _ binders⟩
  | define _ _ _ _ rest =>
    obtain ⟨_, binders⟩ := rest
    exact ⟨_, .seq (.define _ _ _) binders⟩
  | call _ _ _ _ _ _ rest =>
    obtain ⟨_, binders⟩ := rest
    exact ⟨_, .seq (.define _ _ _) (.seq (.assign _ _) (.seq (.assign _ _) binders))⟩

private theorem argument_origins {block : LexicalBlock}
    {arguments : List Lowering.Resolve.SourceExpr} {code : List Lowering.Expr} {reads : List Binding}
    (related : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Arguments block arguments code reads) :
    ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin := by
  induction related with
  | nil => simp
  | cons operand _ ih =>
    intro binding member
    exact (List.mem_append.mp member).elim (Body.operand_origins operand binding) (ih binding)

private theorem assignment_origins {block : LexicalBlock} (site : Site block) (assignment : Assignment block) :
    ∀ binding ∈ assignment.reads site.name, ∃ origin, ReadOrigin block binding origin := by
  intro binding member
  rcases List.mem_cons.mp member with rfl | later
  · exact ⟨.owned, .owned site.target⟩
  · rcases List.mem_cons.mp later with rfl | argument
    · exact ⟨.owned, .owned assignment.copyOwned⟩
    · exact argument_origins assignment.operands binding argument

theorem selects {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    ∃ free, Selects block resolved.reads free := by
  apply selects_of_origins
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.read_origins ordinary
  | assignments leading _ rest =>
    intro binding member
    exact (List.mem_append.mp member).elim (Body.prefix_read_origins leading binding) (rest binding)
  | define site _ _ _ rest =>
    intro binding member
    exact (List.mem_append.mp member).elim (Nested.definition_read_origins site.selects site.lexical binding)
      (rest binding)
  | call site _ assignment _ _ _ rest =>
    intro binding member
    rcases List.mem_append.mp member with own | later
    · exact Nested.definition_read_origins site.selects site.lexical binding own
    · exact (List.mem_append.mp later).elim (assignment_origins site assignment binding) (rest binding)

private def Stable (seed final : Program) (emitted : Emissions) : Prop :=
  PreservesDeclarations seed final ∧ ∀ entry ∈ emitted, final[entry.1]? = some entry.2

private theorem append_links (site : Declaration) {seed childTable final : Program} {descendants later : Emissions}
    (child : Stable seed childTable descendants) (rest : Stable (childTable.push site) final later) :
    Stable seed final (descendants ++ (childTable.size, site) :: later) := by
  have push : PreservesDeclarations childTable (childTable.push site) := by
    intro id entry found
    have within := (Array.getElem?_eq_some_iff.mp found).choose
    simp [Array.getElem?_push, Nat.ne_of_lt within, found]
  have retained : PreservesDeclarations childTable final := fun id entry found => rest.1 id entry (push id entry found)
  refine ⟨fun id entry found => retained id entry (child.1 id entry found), ?_⟩
  intro entry seen
  rcases List.mem_append.mp seen with nested | remaining
  · exact retained _ _ (child.2 entry nested)
  · rcases List.mem_cons.mp remaining with rfl | later
    · exact rest.1 _ _ Array.getElem?_push_size
    · exact rest.2 entry later

theorem links {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    PreservesDeclarations seed final ∧ ∀ entry ∈ emitted, final[entry.1]? = some entry.2 := by
  induction profile with
  | plain ordinary => exact Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.links ordinary
  | assignments _ _ rest => exact rest
  | define site _ _ child rest => exact append_links site.declaration child rest
  | call site _ _ _ _ child rest => exact append_links site.declaration child rest

theorem call_ids {block : LexicalBlock} {source : Statement} {seed final : Program} {resolved : ResolvedBody}
    {emitted : Emissions} {calls : List DeclarationId} (profile : Elaborates block source seed resolved final emitted calls) :
    List.Subset calls (emitted.map Prod.fst) := by
  induction profile with
  | plain => exact List.nil_subset _
  | assignments _ _ rest => exact rest
  | define _ _ _ _ rest =>
    intro id member
    exact List.mem_map.mpr <| (List.mem_map.mp (rest member)).imp
      (fun entry ⟨seen, eq⟩ => ⟨List.mem_append_right _ (List.mem_cons_of_mem _ seen), eq⟩)
  | call _ _ _ _ _ child rest =>
    intro id member
    rcases List.mem_cons.mp member with rfl | later
    · exact List.mem_map.mpr ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩
    · rcases List.mem_append.mp later with nested | suffix
      · exact List.mem_map.mpr <| (List.mem_map.mp (child nested)).imp
          (fun entry ⟨seen, eq⟩ => ⟨List.mem_append_left _ seen, eq⟩)
      · exact List.mem_map.mpr <| (List.mem_map.mp (rest suffix)).imp
          (fun entry ⟨seen, eq⟩ => ⟨List.mem_append_right _ (List.mem_cons_of_mem _ seen), eq⟩)

theorem child_available {block : LexicalBlock} {source : Statement} {seed childTable : Program}
    {code : ResolvedBody} {emitted : Emissions} {childCalls : List DeclarationId}
    (child : Elaborates block source seed code childTable emitted childCalls)
    {available : List DeclarationId} (guarded : List.Subset childCalls available) :
    List.Subset childCalls (withoutDeclaration available childTable.size) := by
  intro id used
  obtain ⟨entry, emitted, index⟩ := List.mem_map.mp (call_ids child used)
  have within := (Array.getElem?_eq_some_iff.mp ((links child).2 entry emitted)).choose
  exact mem_withoutDeclaration.mpr ⟨guarded used, Nat.ne_of_lt (index ▸ within)⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite
