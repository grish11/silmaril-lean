module

public import Silmaril.Formats.Parquet.Int96.Dictionary.File.Defs
import all Silmaril.Formats.Parquet.Int96.Dictionary.File.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.Int96.Dictionary.Thms
import Silmaril.Formats.Parquet.Int96.File.Thms
import Silmaril.Formats.Parquet.FlatColumn.Thms
import Init.Data.List.Sort.Lemmas

public section

namespace Silmaril.Proofs.Formats.Parquet.Int96.Dictionary.File

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Dictionary.File
open Silmaril.Formats.Parquet.Int96.Dictionary (Slots)

variable {name : String} {layout : FlatColumn.Layout} {interpretation : Policy}

theorem select_sound {bound : Int96.File.Checked name layout interpretation}
    {index : Nat} {selected : Selected} (h : select bound index = .ok selected) :
    bound.snapshot.groupAt index = some selected.group ∧
      selected.group.columns[bound.binding.columnOrdinal]? = some selected.column ∧
      selected.column.metadata.pathInSchema = [bound.binding.leaf.name] ∧
      selected.column.metadata.physicalType = .int96 ∧
      selected.column.metadata.numValues = selected.group.numRows ∧
      Parquet.Page.columnSpan bound.snapshot.footer.start selected.column.metadata = some selected.span := by
  unfold select at h
  dsimp only at h
  split at h <;> try contradiction
  rename_i group atGroup
  split at h <;> try contradiction
  rename_i column atColumn
  split at h <;> try contradiction
  rename_i associated
  split at h <;> try contradiction
  rename_i span atSpan
  cases h
  obtain ⟨path, others⟩ := not_or.mp associated
  obtain ⟨physical, rows⟩ := not_or.mp others
  exact ⟨atGroup, atColumn, not_ne_iff.mp path, not_ne_iff.mp physical,
    not_ne_iff.mp rows, atSpan⟩

private theorem neighbors_ordered (ranges : List (Nat × Footer.Span))
    (sorted : ranges.Pairwise (fun left right => byStart left right = true)) (accepted : checkNeighbors ranges = .ok ()) :
    ranges.Pairwise (fun left right => left.2.stop ≤ right.2.start) := by
  induction ranges with
  | nil => exact .nil
  | cons first rest ih =>
    cases rest with
    | nil => exact .cons (by simp) .nil
    | cons second tail =>
      have later := (List.pairwise_cons.mp sorted).2
      have h : first.2.stop ≤ second.2.start := by
        by_contra! invalid
        simp [checkNeighbors, Nat.not_le.mpr invalid] at accepted
      refine .cons ?_ (ih later (by simpa [checkNeighbors, h] using accepted))
      intro other member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact h
      · have start : second.2.start ≤ other.2.start := by
          simpa [byStart] using (List.pairwise_cons.mp later).1 other inTail
        exact Nat.le_trans h start

theorem preflight_sound {bound : Int96.File.Checked name layout interpretation}
    (accepted : preflight bound = .ok ()) :
    ∃ ranges, spans bound = .ok ranges ∧ ranges.Pairwise
      (fun left right => left.2.stop ≤ right.2.start ∨ right.2.stop ≤ left.2.start) := by
  cases read : spans bound with
  | error cause => simp [preflight, read, Bind.bind, Except.bind] at accepted
  | ok ranges =>
    have sorted : (ranges.mergeSort byStart).Pairwise (fun left right => byStart left right = true) :=
      List.pairwise_mergeSort (le := byStart)
        (fun _ _ _ first second => by
          simp only [byStart, decide_eq_true_eq] at first second ⊢
          exact Nat.le_trans first second)
        (fun _ _ => by simpa [byStart, Bool.or_eq_true] using Nat.le_total _ _) ranges
    have checked := neighbors_ordered (ranges.mergeSort byStart) sorted
      (by simpa [preflight, read, Bind.bind, Except.bind] using accepted)
    refine ⟨ranges, rfl, ?_⟩
    exact (checked.imp (fun h => Or.inl h)).perm (List.mergeSort_perm _ _) Or.symm

private theorem mapM_at {α β ε : Type} {read : α → Except ε β}
    {inputs : List α} {outputs : List β} (h : inputs.mapM read = .ok outputs)
    {index : Nat} {input : α} (atInput : inputs[index]? = some input) :
    ∃ output, read input = .ok output ∧ outputs[index]? = some output := by
  induction inputs generalizing outputs index with
  | nil => simp at atInput
  | cons first rest ih =>
    cases firstRead : read first with
    | error cause => simp [List.mapM_cons, firstRead, Bind.bind, Except.bind] at h
    | ok firstOutput =>
      cases restRead : rest.mapM read with
      | error cause => simp [List.mapM_cons, firstRead, restRead, Bind.bind, Except.bind] at h
      | ok tail =>
        have same : firstOutput :: tail = outputs := by
          simpa [List.mapM_cons, firstRead, restRead, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        subst outputs
        cases index with
        | zero =>
          simp at atInput
          subst input
          exact ⟨firstOutput, firstRead, rfl⟩
        | succ index => exact ih restRead atInput

theorem spans_at {bound : Int96.File.Checked name layout interpretation} {ranges : List (Nat × Footer.Span)}
    (h : spans bound = .ok ranges) {index : Nat} (inside : index < bound.snapshot.groupCount) :
    ∃ selected, select bound index = .ok selected ∧ ranges[index]? = some (index, selected.span) := by
  obtain ⟨output, order, located⟩ := mapM_at h (List.getElem?_range inside)
  cases chosen : select bound index with
  | error cause => simp [chosen, Except.map, Except.mapError] at order
  | ok selected =>
    have same : (index, selected.span) = output := by
      simpa [chosen, Except.map, Except.mapError] using order
    exact ⟨selected, rfl, located.trans (congrArg some same.symm)⟩

theorem openFile_sound {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (accepted : openFile limits source name layout interpretation = .ok checked) :
    Int96.File.openFile limits.bindingLimits source name layout interpretation = .ok checked.bound ∧
      preflight checked.bound = .ok () ∧ checked.chunkLimits = limits.chunk := by
  cases opened : Int96.File.openFile limits.bindingLimits source name layout interpretation with
  | error cause => simp [openFile, opened, Bind.bind, Except.bind, Except.mapError] at accepted
  | ok bound =>
    cases structural : preflight bound with
    | error cause => simp [openFile, opened, structural, Bind.bind, Except.bind, Except.mapError] at accepted
    | ok valid =>
      cases valid
      simp [openFile, opened, structural, Bind.bind, Except.bind, Except.mapError,
        Pure.pure, Except.pure] at accepted
      cases accepted
      exact ⟨rfl, structural, rfl⟩

theorem openFile_disjoint {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (accepted : openFile limits source name layout interpretation = .ok checked) :
    ∃ ranges : List (Nat × Footer.Span),
      ranges.Pairwise (fun left right => left.2.stop ≤ right.2.start ∨ right.2.stop ≤ left.2.start) ∧
      ∀ index < checked.bound.snapshot.groupCount, ∃ selected,
        select checked.bound index = .ok selected ∧ ranges[index]? = some (index, selected.span) := by
  obtain ⟨ranges, listed, disjoint⟩ := preflight_sound (openFile_sound accepted).2.1
  exact ⟨ranges, disjoint, fun _ inside => spans_at listed inside⟩

theorem openFile_snapshot {limits : Limits} {source : Bytes} {checked : Checked name layout interpretation}
    (accepted : openFile limits source name layout interpretation = .ok checked) :
    source.length ≤ limits.maxFileBytes ∧
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok checked.bound.snapshot ∧
      checked.bound.snapshot.metadata.numRows.toNat ≤ limits.maxTotalRows ∧
      FlatColumn.bindColumn checked.bound.snapshot ⟨name, .int96, layout⟩ = .ok checked.bound.binding := by
  obtain ⟨bytes, snapshot, rows, binding, _⟩ :=
    Int96.File.openFile_sound (openFile_sound accepted).1
  exact ⟨bytes, snapshot, rows, binding⟩

theorem readGroup_of_selected (checked : Checked name layout interpretation) {index : Nat}
    {selected : Selected} (h : select checked.bound index = .ok selected) :
    checked.readGroup index =
      (Dictionary.read checked.chunkLimits interpretation checked.bound.snapshot.bytes
        checked.bound.snapshot.footer.start selected.group.numRows.toNat checked.bound.binding.leaf
        selected.column.metadata).mapError
          (.chunk index checked.bound.binding.columnOrdinal name) := by
  simp [Checked.readGroup, h, Bind.bind, Except.bind, Except.mapError]

theorem readGroup_wire {checked : Checked name layout interpretation} {index : Nat}
    {slots : Slots interpretation} (decoded : checked.readGroup index = .ok slots) :
    ∃ selected first rest dictionary pages,
      select checked.bound index = .ok selected ∧
      checked.bound.snapshot.metadata.schema[checked.bound.binding.leafOrdinal]? =
        some checked.bound.binding.leaf ∧
      checked.bound.snapshot.groupAt index = some selected.group ∧
      selected.group.columns[checked.bound.binding.columnOrdinal]? = some selected.column ∧
      Parquet.Page.readChunk checked.chunkLimits.framing checked.bound.snapshot.bytes selected.span =
        .ok (first :: rest) ∧
      Parquet.Page.Chain selected.span selected.span.start selected.span.stop (first :: rest) ∧
      selected.column.metadata.dictionaryPageOffset = some (first.header.start : Int) ∧
      rest.head?.map (fun frame => (frame.header.start : Int)) = some selected.column.metadata.dataPageOffset ∧
      Dictionary.readDictionary checked.chunkLimits interpretation checked.bound.snapshot.bytes first =
        .ok dictionary ∧
      List.Forall₂ (fun frame page => ∃ params,
        Dictionary.dataParameters checked.bound.binding.leaf frame.value = .ok params ∧
        Dictionary.decodeData checked.chunkLimits dictionary params
          (Dictionary.frameBody checked.bound.snapshot.bytes frame) = .ok page) rest pages ∧
      slots = pages.flatten ∧ slots.length = selected.group.numRows.toNat := by
  cases chosen : select checked.bound index with
  | error cause => simp [Checked.readGroup, chosen, Bind.bind, Except.bind, Except.mapError] at decoded
  | ok selected =>
    rw [readGroup_of_selected checked chosen] at decoded
    have physical : Dictionary.read checked.chunkLimits interpretation checked.bound.snapshot.bytes
        checked.bound.snapshot.footer.start selected.group.numRows.toNat checked.bound.binding.leaf
        selected.column.metadata = .ok slots := by
      unfold Except.mapError at decoded
      split at decoded <;> rename_i result read
      · contradiction
      · cases decoded
        exact read
    obtain ⟨span, first, rest, dictionary, pages, slice, framed, chain, dictOffset, dataOffset,
      dictionaryOk, ordered, flattened, count⟩ := Dictionary.read_framed_wire physical
    obtain ⟨group, column, _, _, _, spanOk⟩ := select_sound chosen
    have sameSpan : span = selected.span := Option.some.inj (slice.symm.trans spanOk)
    exact ⟨selected, first, rest, dictionary, pages, rfl, checked.bound.binding.leafAt,
      group, column, sameSpan ▸ framed, sameSpan ▸ chain, dictOffset, dataOffset, dictionaryOk, ordered, flattened, count⟩

private theorem loop_sound (checked : Checked name layout interpretation)
    (indices : List Nat) (reversed : List (Slots interpretation)) :
    let trace := Checked.readAll.loop checked indices reversed
    ∃ completed, trace.groups = reversed.reverse ++ completed ∧
      match trace.failure with
      | none => indices.mapM checked.readGroup = .ok completed
      | some cause =>
        ∃ before index after, indices = before ++ index :: after ∧
          before.mapM checked.readGroup = .ok completed ∧ checked.readGroup index = .error cause := by
  induction indices generalizing reversed with
  | nil => exact ⟨[], by simp [Checked.readAll.loop], rfl⟩
  | cons index rest ih =>
    simp only [Checked.readAll.loop]
    cases first : checked.readGroup index with
    | error cause =>
      exact ⟨[], by simp, [], index, rest, rfl, rfl, first⟩
    | ok slots =>
      obtain ⟨completed, ordered, outcome⟩ := ih (slots :: reversed)
      refine ⟨slots :: completed, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using ordered
      · cases failed : (Checked.readAll.loop checked rest (slots :: reversed)).failure with
        | none =>
          simp only [failed] at outcome ⊢
          simp [List.mapM_cons, first, outcome, Bind.bind, Except.bind, Pure.pure, Except.pure]
        | some cause =>
          simp only [failed] at outcome ⊢
          obtain ⟨before, bad, after, rfl, earlier, invalid⟩ := outcome
          refine ⟨index :: before, bad, after, rfl, ?_, invalid⟩
          simp [List.mapM_cons, first, earlier, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem readAll_sound (checked : Checked name layout interpretation) :
    let indices := List.range checked.bound.snapshot.groupCount
    let trace := checked.readAll
    match trace.failure with
    | none => indices.mapM checked.readGroup = .ok trace.groups
    | some cause =>
      ∃ before index after, indices = before ++ index :: after ∧
        before.mapM checked.readGroup = .ok trace.groups ∧ checked.readGroup index = .error cause := by
  obtain ⟨completed, ordered, outcome⟩ := loop_sound checked (List.range checked.bound.snapshot.groupCount) []
  simp only [List.reverse_nil, List.nil_append] at ordered
  cases failed : (Checked.readAll.loop checked (List.range checked.bound.snapshot.groupCount) []).failure <;>
    simpa only [Checked.readAll, ordered, failed] using outcome

private theorem loop_after_prefix (checked : Checked name layout interpretation)
    {before : List Nat} {groups : List (Slots interpretation)}
    (earlier : before.mapM checked.readGroup = .ok groups) (after : List Nat)
    (reversed : List (Slots interpretation)) :
    Checked.readAll.loop checked (before ++ after) reversed =
      Checked.readAll.loop checked after (groups.reverse ++ reversed) := by
  induction before generalizing groups reversed with
  | nil =>
    simp [Pure.pure, Except.pure] at earlier
    subst groups
    rfl
  | cons index before ih =>
    cases first : checked.readGroup index with
    | error cause => simp [List.mapM_cons, first, Bind.bind, Except.bind] at earlier
    | ok slots =>
      cases tail : before.mapM checked.readGroup with
      | error cause => simp [List.mapM_cons, first, tail, Bind.bind, Except.bind] at earlier
      | ok remaining =>
        have allGroups : slots :: remaining = groups := by
          simpa [List.mapM_cons, first, tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using earlier
        subst groups
        simpa [Checked.readAll.loop, first, List.reverse_cons, List.append_assoc] using
          ih tail (slots :: reversed)

theorem readAll_complete {checked : Checked name layout interpretation} {groups : List (Slots interpretation)}
    (decoded : (List.range checked.bound.snapshot.groupCount).mapM checked.readGroup = .ok groups) :
    checked.readAll = ⟨groups, none⟩ := by
  have whole := loop_after_prefix checked decoded [] []
  simpa [Checked.readAll, Checked.readAll.loop] using whole

theorem readAll_first_error {checked : Checked name layout interpretation}
    {before after : List Nat} {index : Nat} {groups : List (Slots interpretation)} {cause : ReadError}
    (split : List.range checked.bound.snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM checked.readGroup = .ok groups)
    (failed : checked.readGroup index = .error cause) :
    checked.readAll = ⟨groups, some cause⟩ := by
  rw [Checked.readAll, split, loop_after_prefix checked earlier]
  simp [Checked.readAll.loop, failed]

end Silmaril.Proofs.Formats.Parquet.Int96.Dictionary.File
