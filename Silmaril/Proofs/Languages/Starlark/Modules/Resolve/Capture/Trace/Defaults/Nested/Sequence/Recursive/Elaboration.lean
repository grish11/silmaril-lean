module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open Silmaril.Languages.Starlark (Binding Scope)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Capture Value)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)

theorem lexical_defaults {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) (named : KeywordLexical parent keywords) :
    Lexical.Elaborates parent site.defaultSources site.defaultsInOrder := by
  cases keywords with
  | nil => exact site.lexical
  | cons first rest => exact Lexical.append site.lexical named

private theorem source_names {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) :
    site.sourceSignature.parameterNames = parameterNames site.parameters keywords varargs kwargs := by
  cases keywords <;> cases varargs <;> cases kwargs <;>
    simp [Site.sourceSignature, SourceSignature.parameterNames, parameterNames, Parameters.source,
      Parameters.names, List.map_map, Function.comp_def]

private theorem parameter_binders {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) :
    Block.ParameterBinders site.sourceSignature (parameterNames site.parameters keywords varargs kwargs) := by
  have ordered (parameters : List SourceParameter) :
      Assignment.InOrder (fun p name => p.name = name) parameters (parameters.map SourceParameter.name) := by
    induction parameters with
    | nil => exact .nil
    | cons first rest ih => exact .cons rfl ih
  rw [← source_names site]
  exact .signature varargs kwargs (ordered _) (ordered _)

theorem compile_site {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) (named : KeywordLexical parent keywords)
    {seed middle : Program} (compiled : compileBody ⟨site.block.context, .local⟩ site.source seed =
      .ok (site.body, middle)) :
    compileBody ⟨parent.context, .local⟩ site.statement seed =
      .ok (⟨.define (fileSlot site.name) middle.size, site.reads⟩, middle.push site.declaration) := by
  let block : BlockContext := ⟨parent.context, .local⟩
  have ⟨same, _⟩ := Lexical.translates site.lexical
  have ⟨_, allTracked⟩ := Lexical.translates (lexical_defaults site named)
  have tracked : ∀ item ∈ site.defaults ++ keywordDefaults keywords,
      Lowering.Resolve.resolveTracked parent.context item.source = .ok (item.value, item.reads) := by
    cases keywords <;> simpa [Site.defaultsInOrder, keywordDefaults] using allTracked
  have sourceSignature : site.sourceSignature =
      { positional := site.parameters.required.map (fun name => ⟨name, none⟩) ++
          site.defaults.map PlainPositionalDefault.parameter
        keywordOnly := keywords.map PlainKeywordParameter.source
        varargs := varargs
        kwargs := kwargs } := by
    simp [Site.sourceSignature, Parameters.source, ← same, List.map_map,
      PlainPositionalDefault.parameter, Function.comp_def]
  have layout := Block.collectFunctionLayout_eq parent.context (parameter_binders site) site.collects site.localOrder
  rw [sourceSignature] at layout
  have emitted := compileBody_plainParameterDefinition block site.name site.parameters.required
    site.defaults keywords varargs kwargs site.source seed middle _ site.body tracked layout compiled
  have captures : captureNames (parameterNames site.parameters keywords varargs kwargs ++ site.locals) site.body.reads = site.free :=
    captureNames_eq site.selects
  have optional : site.defaults.map PlainPositionalDefault.resolved =
      ((site.parameters.optional.map (fileSlot ∘ Prod.fst)).zip (site.defaults.map PlainPositionalDefault.value)).map
        (fun (slot, code) => (⟨slot, some code⟩ : Parameter)) := by
    simp [← same, List.map_map, List.zip_map', PlainPositionalDefault.resolved, Function.comp_def]
  change compileBody block (.define site.name site.sourceSignature site.source) seed = _
  rw [sourceSignature, emitted, optional, ← sourceSignature, source_names site, captures]
  cases keywords <;> simp [Site.declaration, Parameters.signature, Site.reads, Site.defaultsInOrder, keywordDefaults]

private theorem keyword_slots (keywords : List PlainKeywordParameter) :
    (keywords.map PlainKeywordParameter.resolved).map Parameter.slot =
      (keywords.map (SourceParameter.name ∘ PlainKeywordParameter.source)).map fileSlot := by
  induction keywords with
  | nil => rfl
  | cons first rest ih =>
    cases first <;> simp [PlainKeywordParameter.resolved, PlainKeywordParameter.source,
      PlainPositionalDefault.resolved, PlainPositionalDefault.parameter, ih]

theorem site_slots {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) :
    site.declaration.signature.slots ++ site.declaration.locals = site.block.owned.map fileSlot := by
  have length : (site.defaults.map PlainPositionalDefault.value).length = site.parameters.optional.length := by
    simpa using congrArg List.length (Lexical.translates site.lexical).1
  have pos : (site.parameters.signature (site.defaults.map PlainPositionalDefault.value)).positional.map
      Parameter.slot = site.parameters.names.map fileSlot := by
    simpa only [Parameters.signature, Signature.slots, Signature.named, List.map_nil, List.append_nil, Option.toList_none]
      using Body.signature_slots site.parameters [] _ length
  unfold Site.declaration Site.block
  simp only [Signature.slots, Signature.named, List.map_append, pos]
  rw [keyword_slots]
  cases keywords <;> cases varargs <;> cases kwargs <;> simp [parameterNames, List.map_map, Function.comp_def]

private theorem keyword_default_pairs (keywords : List PlainKeywordParameter) :
    (keywords.map PlainKeywordParameter.resolved).filterMap (fun p => p.defaultExpr.map (p.slot, ·)) =
      (keywordDefaults keywords).map (fun item => (fileSlot item.name, item.value)) := by
  induction keywords with
  | nil => rfl
  | cons first rest ih =>
    cases first with
    | required name => exact ih
    | defaulted item => exact congrArg ((fileSlot item.name, item.value) :: ·) ih

theorem default_layout {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent keywords varargs kwargs scope) (named : KeywordLexical parent keywords) :
    site.declaration.signature.defaulted.map Prod.fst = site.defaultKeys ∧
      site.declaration.signature.defaulted.map Prod.snd = site.defaultsInOrder.map PlainPositionalDefault.value := by
  have ⟨same, _⟩ := Lexical.translates site.lexical
  have ⟨sourceOrder, _⟩ := Lexical.translates (lexical_defaults site named)
  have positional :
      ((site.parameters.signature (site.defaults.map PlainPositionalDefault.value)).positional.filterMap
        (fun p => p.defaultExpr.map (p.slot, ·))) =
      site.defaults.map (fun item => (fileSlot item.name, item.value)) := by
    simp [Parameters.signature, requiredSignature, List.filterMap_append, List.filterMap_map, Function.comp_def,
      ← same, List.map_map, List.zip_map']
  have all : site.declaration.signature.defaulted =
      site.defaultsInOrder.map (fun item => (fileSlot item.name, item.value)) := by
    unfold Site.declaration
    simp only [Signature.defaulted, Signature.named, List.filterMap_append, positional, keyword_default_pairs]
    cases keywords <;> simp [Site.defaultsInOrder, keywordDefaults]
  rw [all]
  constructor
  · rw [Site.defaultKeys, ← sourceOrder]
    simp [List.map_map, Function.comp_def]
  · simp [List.map_map, Function.comp_def]

theorem compiles {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    compileBody ⟨block.context, .local⟩ source seed = .ok (resolved, final) := by
  induction profile with
  | straight body => exact Body.compile_suite body _
  | define site leading _ _ child rest =>
    have ⟨same, tracked⟩ := Lexical.translates site.lexical
    have compiled := Body.compile_nested_body site.name site.parameters site.collects site.localOrder
      site.body site.selects site.defaults same tracked _ _ child
    exact Body.compile_prefix leading (compileBody_plainSeq _ _ _ _ _ _ _ _ compiled rest)

theorem collects {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∃ occurrences, Block.BodyBinders source occurrences := by
  induction profile with
  | straight => exact ⟨_, Body.collects _⟩
  | define site _ _ _ _ rest =>
    obtain ⟨_, tail⟩ := rest
    exact ⟨_, Body.collects_prefix _ (.seq (.define site.name site.parameters.source site.source) tail)⟩

theorem read_origins {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∀ binding ∈ resolved.reads, ∃ origin, ReadOrigin block binding origin := by
  induction profile with
  | straight body => exact Body.body_origins body
  | define site leading _ _ _ rest =>
    intro binding member
    rcases List.mem_append.mp member with earlier | remaining
    · exact Body.prefix_read_origins leading binding earlier
    · exact (List.mem_append.mp remaining).elim (Nested.definition_read_origins site.selects site.lexical binding)
        (rest binding)

theorem selects {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    ∃ free, Selects block resolved.reads free :=
  selects_of_origins block (read_origins profile)

private theorem push_preserves (program : Program) (declaration : Declaration) :
    PreservesDeclarations program (program.push declaration) := by
  intro id entry found
  have old := (Array.getElem?_eq_some_iff.mp found).choose
  simp [Array.getElem?_push, Nat.ne_of_lt old, found]

theorem links {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    PreservesDeclarations seed final ∧
      ∀ entry ∈ emissions, final[entry.1]? = some entry.2 := by
  induction profile with
  | straight => exact ⟨fun _ _ found => found, by simp⟩
  | define site _ _ _ child rest =>
    obtain ⟨start, childLinks⟩ := child
    obtain ⟨tailPreserves, tailLinks⟩ := rest
    have throughParent : PreservesDeclarations _ _ := fun id entry found =>
      tailPreserves id entry (push_preserves _ site.declaration id entry found)
    refine ⟨fun id entry found => throughParent id entry (start id entry found), ?_⟩
    intro entry present
    rcases List.mem_append.mp present with descendant | emittedLater
    · exact throughParent entry.1 entry.2 (childLinks entry descendant)
    · rcases List.mem_cons.mp emittedLater with rfl | inTail
      · exact tailPreserves _ _ Array.getElem?_push_size
      · exact tailLinks entry inTail

theorem indices {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) :
    emissions.map Prod.fst = List.range' seed.size emissions.length ∧
      final.size = seed.size + emissions.length := by
  induction profile with
  | straight => simp
  | @define _ _ _ _ _ seed childTable final _ descendants remaining site _ _ _ child rest =>
    obtain ⟨childOrder, childSize⟩ := child
    obtain ⟨tailOrder, tailSize⟩ := rest
    constructor
    · simp only [List.map_append, List.map_cons, childOrder, tailOrder, List.length_append, List.length_cons]
      rw [← List.range'_append_1, Array.size_push, childSize, List.range'_succ]
    · simp only [List.length_append, List.length_cons, tailSize, Array.size_push, childSize]
      omega

private theorem requested {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent keywords varargs kwargs) (before after : List Binding)
    (entry : FreeName) (member : entry ∈ site.free) : entry.source ∈ before ++ site.reads ++ after := by
  have seen : entry.source ∈ site.reads := List.mem_append_right _ (List.mem_map.mpr ⟨_, member, rfl⟩)
  simp only [List.mem_append, seen, or_true, true_or]

theorem forwarding_request {parent : LexicalBlock} (site : Site parent)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    (binding : Binding) (present : (⟨binding, binding⟩ : FreeName) ∈ site.free) :
    (⟨binding, binding⟩ : FreeName) ∈ free ↔ binding.scope = .global ∨ binding.name ∉ parent.owned := by
  rw [selected_member selected binding]
  exact and_iff_right (requested site before after _ present)

theorem installs {parent : LexicalBlock} {keywords : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent keywords varargs kwargs)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects parent (before ++ site.reads ++ after) free)
    {state : State} {floor : Nat} (frame : Body.Frame parent free floor state) :
    ∃ captures, Installs state site.free captures ∧ Body.CaptureCells state captures := by
  exact Nested.installs_from_frame site.selects selected (requested site before after) frame

theorem activate_address {parent : LexicalBlock} (site : Site parent)
    {defining : State} {captures : List Capture} (installed : Installs defining site.free captures)
    (caller : State) (assigned : List (Binding × Value))
    (binding : Binding) (address : Nat) (present : (⟨binding, binding⟩ : FreeName) ∈ site.free)
    (origin : Forwarding.HasAddress defining binding address) :
    (activate caller site.declaration captures assigned).slots binding =
      some (.captured address (binding.scope == .local)) := by
  have codeLength : (site.defaults.map PlainPositionalDefault.value).length = site.parameters.optional.length := by
    simpa using congrArg List.length (Lexical.translates site.lexical).1
  exact Nested.activate_address site.selects (Body.signature_slots site.parameters site.locals _ codeLength)
    installed caller assigned binding address present origin

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
          ((site.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values) evaluated) := by
  obtain ⟨captures, installed, live⟩ := installs site selected frame
  obtain ⟨out, ran, exec, meaning, saved⟩ :=
    Lexical.defines_total program available (fileSlot site.name) id site.parameters site.declaration
      site.lexical found rfl state captures installed
  exact ⟨captures, out, installed, live, ran, exec, meaning, saved⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
