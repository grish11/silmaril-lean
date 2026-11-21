module

public import Silmaril.Formats.Git.Translate.Graph.Defs

public section

namespace Silmaril.Proofs.Formats.Git.Graph

open Silmaril.Formats.Git Silmaril.Formats.Git.Translate Silmaril.Formats.Git.Translate.Graph Silmaril.Semantics

variable {Key Source Target Meta : Type} {algorithm : Native.Algorithm}

private theorem plan_step {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    {kind : Kind} {source : Source} {finish : Address Source} (plan : Plan native lookup (.local (kind := kind)) source)
    (edge : LocalEdge lookup (kind, source) finish) : Nonempty (Plan native lookup (.local (kind := finish.1)) finish.2) := by
  obtain ⟨binding, index, read, role, rfl⟩ := edge
  cases plan with
  | found _ other hit _ children =>
    have same := Read.found.inj (hit.symm.trans read)
    subst other
    exact ⟨role ▸ children index⟩

theorem plan_reaches {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    {root finish : Address Source} (plan : Plan native lookup (.local (kind := root.1)) root.2)
    (reachable : Reaches lookup root finish) : Nonempty (Plan native lookup (.local (kind := finish.1)) finish.2) := by
  induction reachable with
  | here => exact ⟨plan⟩
  | step _ edge ih =>
    obtain ⟨localPlan⟩ := ih
    exact plan_step localPlan edge

theorem plan_accessible {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    {kind : Kind} {role : Role kind} {source : Source} (plan : Plan native lookup role source) :
    role = .local → Acc (fun child parent => LocalEdge lookup parent child) (kind, source) := by
  induction plan with
  | external => intro impossible; contradiction
  | found _ binding read _ _ ih =>
    intro _
    refine Acc.intro _ fun finish edge => ?_
    obtain ⟨other, index, hit, role, rfl⟩ := edge
    have same := Read.found.inj (read.symm.trans hit)
    subst other
    exact ih index role

private theorem sequence_ofFn {Item : Type} {count : Nat} (items : Fin count → Item) :
    (List.ofFn (fun index => some (items index))).mapM id = some (List.ofFn items) := by
  rw [show List.ofFn (fun index => some (items index)) = (List.ofFn items).map some from List.map_ofFn.symm,
    List.mapM_map]
  simp only [Function.comp_def, id_eq, ← Option.pure_def]
  exact (List.mapM_pure (f := id)).trans (congrArg pure (List.map_id _))

theorem plan_native {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    {kind : Kind} {role : Role kind} {source : Source} (plan : Plan native lookup role source) :
    Native.renderObject native plan.expand = some plan.expected := by
  induction plan with
  | external => simp only [Plan.expand, Plan.expected, Native.renderObject]
  | found _ binding _ valid children ih =>
    cases binding with
    | mk node bytes =>
      cases node with
      | blob payload =>
        have same : some (Native.loose .blob payload) = some bytes := valid.1
        simp only [Plan.expand, Plan.expected, Node.expand, Native.renderObject]
        rw [Option.some.inj same]
      | tree dir =>
        rcases dir with ⟨keys, entries⟩
        simp only [Plan.expand, Plan.expected, Node.expand, Native.renderObject]
        rw [funext ih]
        unfold Native.renderDir
        have ready : ∀ key (hit : key ∈ keys), (some (children ⟨key, hit⟩).expected).isSome = true := fun _ _ => rfl
        rw [dite_eq_left ready]
        simp only [Option.get_some, Plan.expectedName, Node.edge, Option.bind_eq_bind, Option.pure_def]
        obtain ⟨payload, serialized, same⟩ := Option.map_eq_some_iff.mp valid.1
        rw [serialized]
        exact congrArg (some ∘ Native.View.encoded) same
      | commit data =>
        obtain ⟨tree, parents, metadata⟩ := data
        simp only [Plan.expand, Plan.expected, Node.expand, Native.renderObject]
        rw [ih none, show (List.ofFn fun index => Native.renderObject native (children (some index)).expand) =
          List.ofFn (fun index => some (children (some index)).expected) from congrArg List.ofFn (funext fun index => ih (some index)),
          sequence_ofFn]
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Plan.expectedName, List.map_ofFn,
          Function.comp_def, Node.edge, List.ofFn_get]
        have serialized : Native.commitBytes? native.names ⟨tree, parents, metadata⟩ = some bytes := valid.1
        rw [serialized]
        rfl

private theorem Plan.expand_transport {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    {kind : Kind} {source : Source} {before after : Role kind} (role : before = after)
    (plan : Plan native lookup before source) : (role ▸ plan : Plan native lookup after source).expand = plan.expand := by
  cases role
  rfl

private theorem step_result [DecidableEq Key] {profile : Profile algorithm Key Source Target Meta}
    {lookup : Lookup Key Source} {kind : Kind} {source : Source} {finish : Address Source}
    (plan : Plan profile.native lookup (.local (kind := kind)) source) {result : Result Source Target}
    (translated : translate profile plan.expand = some result) (edge : LocalEdge lookup (kind, source) finish) :
    ∃ childPlan : Plan profile.native lookup (.local (kind := finish.1)) finish.2, ∃ child,
      translate profile childPlan.expand = some child ∧ child.trace.events ⊆ result.trace.events := by
  obtain ⟨binding, index, read, role, rfl⟩ := edge
  cases plan with
  | found _ other hit _ children =>
    have same := Read.found.inj (hit.symm.trans read)
    subst other
    refine ⟨role ▸ children index, ?_⟩
    rw [Plan.expand_transport]
    cases binding with
    | mk node bytes =>
      cases node with
      | blob => exact index.elim
      | tree entries => exact translate_tree_child profile translated index
      | commit data =>
        cases index with
        | none => exact (translate_commit_children profile translated).1
        | some index => exact (translate_commit_children profile translated).2 index

private theorem reaches_result [DecidableEq Key] {profile : Profile algorithm Key Source Target Meta}
    {lookup : Lookup Key Source} {root finish : Address Source}
    (plan : Plan profile.native lookup (.local (kind := root.1)) root.2) {result : Result Source Target}
    (translated : translate profile plan.expand = some result) (reachable : Reaches lookup root finish) :
    ∃ childPlan : Plan profile.native lookup (.local (kind := finish.1)) finish.2, ∃ child,
      translate profile childPlan.expand = some child ∧ child.trace.events ⊆ result.trace.events := by
  induction reachable with
  | here => exact ⟨plan, result, translated, fun {_} member => member⟩
  | step _ edge ih =>
    obtain ⟨startPlan, start, startHit, inside⟩ := ih
    obtain ⟨childPlan, child, hit, included⟩ := step_result startPlan startHit edge
    exact ⟨childPlan, child, hit, fun {_} member => inside (included member)⟩

theorem outcome_reaches [DecidableEq Key] [DecidableEq Source] [DecidableEq Target]
    {profile : Profile algorithm Key Source Target Meta} {lookup : Lookup Key Source} {kind : Kind} {source : Source}
    (outcome : Outcome profile lookup kind source) {finish : Address Source}
    (reachable : Reaches lookup (kind, source) finish) :
    ∃ (target : Target) (bytes : ByteArray), lookup.observed finish.1 finish.2 bytes ∧
      ⟨finish.1, finish.2, target, some bytes⟩ ∈ outcome.result.trace.events := by
  obtain ⟨tag, name⟩ := finish
  obtain ⟨childPlan, child, translated, included⟩ := reaches_result outcome.plan outcome.translated reachable
  obtain ⟨view, native, witness⟩ := translate_native profile childPlan.expand translated
  have sameView := Option.some.inj (native.symm.trans (plan_native childPlan))
  subst view
  have sameName : child.source = name := witness.1.symm.trans childPlan.expectedName
  cases childPlan with
  | found source binding read _ _ =>
    have stored : child.trace.preimages tag child.source binding.bytes := witness.2
    obtain ⟨target, member⟩ := stored
    exact ⟨target, binding.bytes, by simp [Lookup.observed, read], sameName ▸ included member⟩

theorem outcome_audited [DecidableEq Key] [DecidableEq Source] [DecidableEq Target]
    {profile : Profile algorithm Key Source Target Meta} {lookup : Lookup Key Source} {kind : Kind} {source : Source}
    (outcome : Outcome profile lookup kind source) {wire : Wire Target} (wireOK : wire.Agrees outcome.result.target) :
    Audit outcome.result lookup.observed (nativeNames profile.native) wire (externalNames profile) := by
  refine ⟨?_, ?_, wireOK, ?_, ?_⟩
  · intro tag name bytes present
    obtain ⟨target, member⟩ := present
    exact (outcome.checked (⟨tag, name, target, some bytes⟩ : Event Source Target) (Multiset.mem_toFinset.mpr member)).1
  · intro tag name bytes present
    obtain ⟨target, member⟩ := present
    exact (outcome.checked (⟨tag, name, target, some bytes⟩ : Event Source Target) (Multiset.mem_toFinset.mpr member)).2
  · intro tag name first second firstHit secondHit
    obtain ⟨left, leftHit⟩ := firstHit
    obtain ⟨right, rightHit⟩ := secondHit
    exact outcome.consistent ⟨tag, name, first, left⟩ (Multiset.mem_toFinset.mpr leftHit)
      ⟨tag, name, second, right⟩ (Multiset.mem_toFinset.mpr rightHit) rfl rfl
  · intro tag name target member
    exact outcome.checked ⟨tag, name, target, none⟩ (Multiset.mem_toFinset.mpr member)

private theorem plan_result_name [DecidableEq Key] {profile : Profile algorithm Key Source Target Meta}
    {lookup : Lookup Key Source} {kind : Kind} {role : Role kind} {source : Source}
    (plan : Plan profile.native lookup role source) {result : Result Source Target}
    (translated : translate profile plan.expand = some result) : result.source = source := by
  obtain ⟨view, rendered, witness⟩ := translate_native profile plan.expand translated
  have same := Option.some.inj (rendered.symm.trans (plan_native plan))
  exact witness.1.symm.trans (same.symm ▸ plan.expectedName)

theorem outcome_commit [DecidableEq Key] [DecidableEq Source] [DecidableEq Target]
    {profile : Profile algorithm Key Source Target Meta} {lookup : Lookup Key Source} {source : Source}
    (outcome : Outcome profile lookup .commit source) {wire : Wire Target} (wireOK : wire.Agrees outcome.result.target) :
    ∃ (data : Commit Source Source Native.CommitMetadata) (bytes : ByteArray) (tree : Result Source Target)
      (parents : List (Result Source Target)),
      lookup .commit source = .found ⟨.commit data, bytes⟩ ∧ tree.nativeCommit parents data.metadata = data ∧
      CommitEvidence profile tree parents data.metadata outcome.result lookup.observed (nativeNames profile.native) wire := by
  have audit := outcome_audited outcome wireOK
  obtain ⟨plan, _, result, translated, _, _, _⟩ := outcome
  cases plan with
  | found _ binding read _ children =>
    obtain ⟨node, bytes⟩ := binding
    cases node with
    | commit data =>
      obtain ⟨tree, parents, treeHit, parentHits, evidence⟩ := translate_commit_evidence profile translated audit
      refine ⟨data, bytes, tree, parents, read, ?_, evidence⟩
      have treeName := plan_result_name (children none) treeHit
      have lengths := parentHits.length_eq
      rw [List.length_ofFn] at lengths
      have parentNames : parents.map Result.source = data.parents := by
        apply List.ext_get (by simpa only [List.length_map] using lengths.symm)
        intro index left right
        have input : index < (List.ofFn (α := Object Key Source Native.CommitMetadata .commit)
          fun (slot : Fin data.parents.length) =>
          (children (some slot)).expand).length := by simpa
        have output : index < parents.length := lengths ▸ right
        have hit := parentHits.get input output
        rw [List.get_ofFn, Fin.cast_mk] at hit
        simpa only [List.get_eq_getElem, List.getElem_map] using plan_result_name (children (some ⟨index, right⟩)) hit
      cases data
      simp [Result.nativeCommit, treeName, parentNames]

end Silmaril.Proofs.Formats.Git.Graph
