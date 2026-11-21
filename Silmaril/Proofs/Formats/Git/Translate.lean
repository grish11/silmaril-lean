module

public import Silmaril.Formats.Git.Translate.Defs

public section

namespace Silmaril.Proofs.Formats.Git

open Silmaril.Formats.Git Silmaril.Formats.Git.Translate Silmaril.Semantics

variable {Key Source Target Meta : Type} {algorithm : Native.Algorithm}

private theorem materialize_pair (assign : ByteArray → Source) (kind : Kind) (bytes : ByteArray)
    (target : Dasl.Rendered Target) (children : Trace Source Target) :
    (materialize assign kind bytes target children).RootPair kind :=
  ⟨some bytes, by simp [materialize, Trace.union, Trace.observe]⟩

theorem translate_root_pair [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {kind : Kind} (object : Object Key Source Native.CommitMetadata kind) {result : Result Source Target}
    (hit : translate profile object = some result) : result.RootPair kind := by
  cases object with
  | ref kind source =>
    simp only [translate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hit
    obtain ⟨target, _, rfl⟩ := hit
    exact ⟨none, by simp [Trace.opaque, Dasl.Rendered.opaque]⟩
  | blob bytes =>
    simp only [translate, Option.some.injEq] at hit
    subst result
    exact materialize_pair ..
  | tree keys modes children =>
    simp only [translate] at hit
    split at hit
    · simp only [treeStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hit
      obtain ⟨payload, _, target, _, rfl⟩ := hit
      exact materialize_pair ..
    · contradiction
  | commit tree count parents metadata =>
    simp only [translate, commitStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hit
    obtain ⟨root, _, ancestors, _, bytes, _, rfl⟩ := hit
    exact materialize_pair ..

theorem commit_step_evidence (profile : Profile algorithm Key Source Target Meta)
    {tree : Result Source Target} {parents : List (Result Source Target)} {metadata : Native.CommitMetadata}
    {result : Result Source Target} {observed : Kind → Naming.Relation Source ByteArray}
    {nativeNames : Naming.Relation Source ByteArray} {wire : Wire Target}
    {allowedFrontier : Correspondence Source Target}
    (hit : commitStep profile tree parents metadata = some result) (treePair : tree.RootPair .tree)
    (parentPairs : ∀ parent ∈ parents, Result.RootPair .commit parent)
    (audit : Audit result observed nativeNames wire allowedFrontier) :
    CommitEvidence profile tree parents metadata result observed nativeNames wire := by
  simp only [commitStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hit
  obtain ⟨bytes, serialized, rfl⟩ := hit
  refine ⟨materialize_pair .., ?_, ?_, ?_, ?_⟩
  · obtain ⟨wire, present⟩ := treePair
    exact ⟨wire, by simp [materialize, Trace.union, present]⟩
  · intro parent member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    obtain ⟨wire, present⟩ := parentPairs _ member
    refine ⟨wire, ?_⟩
    simp only [materialize, Trace.union, Trace.collect, Multiset.mem_add, Multiset.mem_bind]
    exact Or.inr (Or.inr ⟨index, Finset.mem_val.mpr (Finset.mem_univ _), present⟩)
  · have recorded : (materialize profile.native.assign .commit bytes
        (Dasl.renderCommit profile.naming profile.codec tree.target (parents.map Result.target)
          (profile.metadata metadata)) (tree.trace.union (Trace.collect (Result.trace ∘ parents.get)))).trace.preimages
        .commit (profile.native.assign bytes) bytes := ⟨_, Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _))⟩
    exact ⟨bytes, serialized, audit.observedBytes .commit recorded, audit.nativeNamed .commit recorded⟩
  · dsimp only
    have stored : (Dasl.renderCommit profile.naming profile.codec tree.target (parents.map Result.target)
        (profile.metadata metadata)).store.objects
        (Dasl.renderCommit profile.naming profile.codec tree.target (parents.map Result.target)
          (profile.metadata metadata)).root
        ((Dasl.namedCommit profile.codec).encode (tree.targetCommit profile parents metadata)) := by
      apply Or.inl
      simp [Dasl.renderCommit, Dasl.Rendered.object, Result.targetCommit, List.map_map, Function.comp_def]
    obtain ⟨wireBytes, encodes, named⟩ := audit.targetWire.1 _ _ stored
    exact ⟨(Dasl.namedCommit profile.codec).recovers _, wireBytes, stored, encodes, named⟩

private theorem mapM_forall₂ {Input Output : Type} (visit : Input → Option Output)
    {input : List Input} {output : List Output} (hit : input.mapM visit = some output) :
    List.Forall₂ (fun item result => visit item = some result) input output := by
  induction input generalizing output with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hit
    subst output
    exact .nil
  | cons item tail ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hit
    obtain ⟨first, visited, rest, done, rfl⟩ := hit
    exact .cons visited (ih done)

private theorem forall₂_right {Input Output : Type} {rel : Input → Output → Prop} {input : List Input}
    {output : List Output} (related : List.Forall₂ rel input output) {result : Output} (hit : result ∈ output) :
    ∃ item, rel item result := by
  induction related with
  | nil => simp at hit
  | cons head _ ih =>
    rcases List.mem_cons.mp hit with rfl | tail
    · exact ⟨_, head⟩
    · exact ih tail

private theorem mapM_ofFn {Output : Type} {count : Nat} (visit : Fin count → Option Output) :
    (List.ofFn visit).mapM id = (List.finRange count).mapM visit := by
  rw [show List.ofFn visit = (List.ofFn id).map visit from List.map_ofFn.symm, List.mapM_map]
  rfl

theorem translate_tree_child [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {keys : Finset Key} {modes : ↥keys → EntryMode}
    {children : (key : ↥keys) → Object Key Source Native.CommitMetadata (modes key).kind}
    {result : Result Source Target} (hit : translate profile (.tree keys modes children) = some result)
    (key : ↥keys) : ∃ child, translate profile (children key) = some child ∧
      child.trace.events ⊆ result.trace.events := by
  simp only [translate] at hit
  split at hit
  next present =>
    simp only [treeStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hit
    obtain ⟨_, _, _, _, rfl⟩ := hit
    refine ⟨_, (Option.some_get (present key.val key.property)).symm, fun {event} member => ?_⟩
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_bind.mpr ⟨key, Finset.mem_val.mpr (Finset.mem_univ _), member⟩))
  next => contradiction

theorem translate_commit_children [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {tree : Object Key Source Native.CommitMetadata .tree} {count : Nat}
    {parents : Fin count → Object Key Source Native.CommitMetadata .commit} {metadata : Native.CommitMetadata}
    {result : Result Source Target} (hit : translate profile (.commit tree count parents metadata) = some result) :
    (∃ child, translate profile tree = some child ∧ child.trace.events ⊆ result.trace.events) ∧
    (∀ index, ∃ child, translate profile (parents index) = some child ∧ child.trace.events ⊆ result.trace.events) := by
  simp only [translate, commitStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hit
  obtain ⟨root, treeHit, ancestors, ancestorsHit, _, _, rfl⟩ := hit
  refine ⟨⟨root, treeHit, fun {_} member => Multiset.mem_add.mpr (Or.inr (Multiset.mem_add.mpr (Or.inl member)))⟩,
    fun index => ?_⟩
  rw [mapM_ofFn] at ancestorsHit
  have related := mapM_forall₂ (fun index => translate profile (parents index)) ancestorsHit
  have left : index.val < (List.finRange count).length := by simp
  have right : index.val < ancestors.length := related.length_eq ▸ left
  refine ⟨ancestors.get ⟨index, right⟩, ?_, fun {_} member => ?_⟩
  · simpa only [List.get_finRange, Fin.cast_mk] using related.get left right
  · exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_add.mpr (Or.inr
      (Multiset.mem_bind.mpr ⟨(⟨index, right⟩ : Fin ancestors.length), Finset.mem_val.mpr (Finset.mem_univ _), member⟩))))

private theorem mapM_project {Input Output View Value : Type} (visit : Input → Option View)
    (project : View → Value) (value : Output → Value) {input : List Input} {output : List Output}
    (related : List.Forall₂ (fun item result => ∃ view, visit item = some view ∧ project view = value result)
      input output) : ∃ views, input.mapM visit = some views ∧ views.map project = output.map value := by
  induction related with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons head _ ih =>
    obtain ⟨first, visited, same⟩ := head
    obtain ⟨rest, done, equal⟩ := ih
    exact ⟨first :: rest, by simp [List.mapM_cons, visited, done], by simp [same, equal]⟩

private theorem materialize_source (assign : ByteArray → Source) (kind : Kind) (bytes : ByteArray)
    (target : Dasl.Rendered Target) (children : Trace Source Target) :
    (materialize assign kind bytes target children).SourceWitness assign kind (.encoded bytes) :=
  ⟨rfl, target.root, by simp [materialize, Trace.union, Trace.observe]⟩

theorem translate_native [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {kind : Kind} (object : Object Key Source Native.CommitMetadata kind) {result : Result Source Target}
    (hit : translate profile object = some result) :
    ∃ view, Native.renderObject profile.native object = some view ∧
      result.SourceWitness profile.native.assign kind view := by
  induction object generalizing result with
  | ref kind source =>
    simp only [translate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hit
    obtain ⟨target, _, rfl⟩ := hit
    exact ⟨.opaque source, by rw [Native.renderObject], rfl,
      by simp [Trace.frontier, Trace.opaque, Dasl.Rendered.opaque]⟩
  | blob bytes =>
    simp only [translate, Option.some.injEq] at hit
    subst result
    exact ⟨.encoded (Native.loose .blob bytes), by rw [Native.renderObject], materialize_source ..⟩
  | tree keys modes children ih =>
    simp only [translate] at hit
    split at hit
    next present =>
      let results := fun (key : ↥keys) => (translate profile (children key)).get (present key.val key.property)
      have agreement (key : ↥keys) := ih key (Option.some_get (present key.val key.property)).symm
      let views := fun key => (agreement key).choose
      have visits : (fun key => Native.renderObject profile.native (children key)) = fun key => some (views key) :=
        funext fun key => (agreement key).choose_spec.1
      have names : (fun key : ↥keys => (views key).target profile.native.assign) = fun key => (results key).source :=
        funext fun key => (agreement key).choose_spec.2.1
      change treeStep profile keys modes results = some result at hit
      simp only [treeStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hit
      obtain ⟨payload, serialized, target, _, rfl⟩ := hit
      refine ⟨.encoded (Native.loose .tree payload), ?_, materialize_source ..⟩
      rw [Native.renderObject, visits]
      unfold Native.renderDir
      have ready : ∀ key (member : key ∈ keys), (some (views ⟨key, member⟩)).isSome = true := fun _ _ => rfl
      rw [dite_eq_left ready]
      simp only [Option.get_some, Option.bind_eq_bind, Option.pure_def]
      have dirEq : (⟨keys, fun key => ⟨modes key, (views key).target profile.native.assign⟩⟩ : ShallowTree Key Source) =
          ⟨keys, fun key => ⟨modes key, (results key).source⟩⟩ := by
        congr 1
        exact funext fun key => congrArg (Entry.mk (modes key)) (congrFun names key)
      rw [dirEq, serialized]
      rfl
    next => contradiction
  | commit tree count parents metadata treeIH parentIH =>
    simp only [translate, commitStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hit
    obtain ⟨root, treeHit, ancestors, ancestorsHit, bytes, serialized, rfl⟩ := hit
    obtain ⟨treeView, treeVisit, treeName, _⟩ := treeIH treeHit
    rw [mapM_ofFn] at ancestorsHit
    have related : List.Forall₂ (fun index ancestor => ∃ view,
        Native.renderObject profile.native (parents index) = some view ∧
          view.target profile.native.assign = ancestor.source) (List.finRange count) ancestors :=
      (mapM_forall₂ _ ancestorsHit).imp fun index _ visited =>
      let ⟨view, nativeVisit, name, _⟩ := parentIH index visited
      ⟨view, nativeVisit, name⟩
    obtain ⟨parentViews, parentVisit, parentNames⟩ :=
      mapM_project _ (Native.View.target profile.native.assign) Result.source related
    refine ⟨.encoded bytes, ?_, materialize_source ..⟩
    rw [Native.renderObject, mapM_ofFn, treeVisit, parentVisit]
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some]
    rw [treeName, parentNames, ← Result.nativeCommit, serialized]
    rfl

theorem translate_commit_evidence [DecidableEq Key] (profile : Profile algorithm Key Source Target Meta)
    {tree : Object Key Source Native.CommitMetadata .tree} {count : Nat}
    {parents : Fin count → Object Key Source Native.CommitMetadata .commit} {metadata : Native.CommitMetadata}
    {result : Result Source Target} {observed : Kind → Naming.Relation Source ByteArray}
    {nativeNames : Naming.Relation Source ByteArray} {wire : Wire Target}
    {allowedFrontier : Correspondence Source Target}
    (hit : translate profile (.commit tree count parents metadata) = some result)
    (audit : Audit result observed nativeNames wire allowedFrontier) :
    ∃ root ancestors, translate profile tree = some root ∧
      List.Forall₂ (fun parent translated => translate profile parent = some translated) (List.ofFn parents) ancestors ∧
      CommitEvidence profile root ancestors metadata result observed nativeNames wire := by
  simp only [translate, Option.bind_eq_bind, Option.bind_eq_some_iff] at hit
  obtain ⟨root, treeHit, ancestors, ancestorsHit, done⟩ := hit
  rw [show (List.ofFn fun index => translate profile (parents index)) =
    (List.ofFn parents).map (translate profile) from List.map_ofFn.symm, List.mapM_map] at ancestorsHit
  have related := mapM_forall₂ (translate profile) ancestorsHit
  refine ⟨root, ancestors, treeHit, related, commit_step_evidence profile done
    (translate_root_pair profile tree treeHit) ?_ audit⟩
  intro ancestor present
  obtain ⟨parent, visited⟩ := forall₂_right related present
  exact translate_root_pair profile parent visited

end Silmaril.Proofs.Formats.Git
