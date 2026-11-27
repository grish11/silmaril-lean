module

public import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Defs
import Silmaril.Formats.Hive.PartitionPath.Positional.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.PartitionPath.Positional

open Silmaril.Formats.Hive.PartitionPath
open Silmaril.Formats.Hive.PartitionPath.Positional

private theorem decode_encodeSegment (encoding : Encoding) (text : String)
    (nonempty : (encodeSegment encoding text).isEmpty = false) :
    decodeSegment encoding (encodeSegment encoding text) = .ok text := by
  simp only [decodeSegment, nonempty, Bool.false_eq_true, ↓reduceIte]
  cases encoding <;> simp [encodeSegment, Percent.decode_encode]

private theorem segment_spec {maximum : Nat} {encoding : Encoding} {options : Options}
    {entry : Entry} {segment : String}
    (rendered : Positional.renderSegment maximum encoding options entry = .ok segment) :
    ∃ text, entry.2 = some text ∧ decodeSegment encoding segment = .ok text ∧
      segment ≠ "" ∧ '/' ∉ segment.toList ∧ segment.utf8ByteSize ≤ maximum := by
  obtain ⟨key, _ | text⟩ := entry
  · cases rendered
  by_cases marker : text = options.nullMarker
  · simp [Positional.renderSegment, marker, bind, Except.bind] at rendered
  by_cases empty : (encodeSegment encoding text).isEmpty = true
  · simp [Positional.renderSegment, marker, empty, bind, Except.bind] at rendered
  by_cases blocked : unsafeSegment (encodeSegment encoding text)
  · simp [Positional.renderSegment, marker, empty, blocked, bind, Except.bind] at rendered
  by_cases oversized : (encodeSegment encoding text).utf8ByteSize > maximum
  · simp [Positional.renderSegment, marker, empty, blocked, oversized, bind, Except.bind] at rendered
  simp [Positional.renderSegment, marker, empty, blocked, oversized,
    pure, Except.pure] at rendered
  subst segment
  exact ⟨text, rfl, decode_encodeSegment encoding text (Bool.eq_false_iff.mpr empty),
    fun eq => empty (by simp [eq]), fun slash => blocked (.inr (.inr (.inl slash))),
    Nat.le_of_not_gt oversized⟩

private theorem segments_spec {maximum : Nat} {encoding : Encoding} {options : Options}
    {entries : Partition} {raw : List String}
    (rendered : entries.mapM (Positional.renderSegment maximum encoding options) = .ok raw) :
    raw.length = entries.length ∧
      (∃ texts, raw.mapM (decodeSegment encoding) = .ok texts ∧
        entries = (entries.map Prod.fst).zip (texts.map some)) ∧
      ∀ segment ∈ raw, segment ≠ "" ∧ '/' ∉ segment.toList ∧ segment.utf8ByteSize ≤ maximum := by
  induction entries generalizing raw with
  | nil =>
    cases rendered
    exact ⟨rfl, ⟨[], rfl, rfl⟩, by simp⟩
  | cons entry rest ih =>
    rw [List.mapM_cons] at rendered
    cases head : Positional.renderSegment maximum encoding options entry with
    | error error => simp [head, bind, Except.bind] at rendered
    | ok segment =>
      cases tail : rest.mapM (Positional.renderSegment maximum encoding options) with
      | error error => simp [head, tail, bind, Except.bind] at rendered
      | ok more =>
        simp [head, tail, bind, Except.bind, pure, Except.pure] at rendered
        subst raw
        obtain ⟨text, present, read, safe⟩ := segment_spec head
        obtain ⟨count, ⟨texts, readRest, ordered⟩, safeRest⟩ := ih tail
        exact ⟨by simp [count],
          ⟨text :: texts, by simp [List.mapM_cons, read, readRest, bind, Except.bind, pure, Except.pure],
            by simpa using ⟨Prod.ext rfl present, ordered⟩⟩,
          fun item member => (List.mem_cons.mp member).elim (fun eq => eq ▸ safe) (safeRest item)⟩

private theorem segments_intercalate (raw : List String)
    (safe : ∀ segment ∈ raw, segment ≠ "" ∧ '/' ∉ segment.toList) :
    segments ("/".intercalate raw) = raw := by
  cases raw with
  | nil => simp [segments]
  | cons first rest =>
    have separated := splitOn_slash_intercalate first rest (fun segment hit => (safe segment hit).2)
    have nonempty : ("/".intercalate (first :: rest)).isEmpty = false := by
      cases rest with
      | nil => simpa [String.isEmpty_iff] using (safe first (by simp)).1
      | cons next tail => simp
    simp [segments, separated, nonempty]

theorem render_spec {limits : RenderLimits} {keys : List String} {encoding : Encoding}
    {options : Options} {entries : Partition} {directory : String}
    (rendered : Positional.render limits keys encoding options entries = .ok directory) :
    parse limits.maxDirectoryBytes keys encoding options directory = .ok entries ∧
      directory.utf8ByteSize ≤ limits.maxDirectoryBytes ∧ (segments directory).length = keys.length ∧
      ∀ segment ∈ segments directory, segment.utf8ByteSize ≤ limits.maxSegmentBytes := by
  by_cases emptyMarker : options.nullMarker.isEmpty = true
  · simp [Positional.render, emptyMarker, bind, Except.bind] at rendered
  by_cases named : entries.map Prod.fst = keys
  · cases valid : validate options entries with
    | error reason => simp [Positional.render, emptyMarker, named, valid, bind, Except.bind, Except.mapError] at rendered
    | ok accepted =>
      cases encoded : entries.mapM (Positional.renderSegment limits.maxSegmentBytes encoding options)
      · simp [Positional.render, emptyMarker, named, valid, encoded, bind, Except.bind, Except.mapError] at rendered
      · rename_i raw
        by_cases oversized : ("/".intercalate raw).utf8ByteSize > limits.maxDirectoryBytes
        · simp [Positional.render, emptyMarker, named, valid, encoded, bind, Except.bind, Except.mapError,
            oversized] at rendered
        simp [Positional.render, emptyMarker, named, valid, encoded, bind, Except.bind, Except.mapError,
          oversized, pure, Except.pure] at rendered
        subst directory
        obtain ⟨count, ⟨texts, read, ordered⟩, safe⟩ := segments_spec encoded
        have separated := segments_intercalate raw (fun segment hit => ⟨(safe segment hit).1, (safe segment hit).2.1⟩)
        have arity : raw.length = keys.length := by rw [← named, List.length_map, count]
        have limit := Nat.le_of_not_gt oversized
        refine ⟨?_, limit, by simpa only [separated] using arity,
          fun segment hit => (safe segment (by simpa only [separated] using hit)).2.2⟩
        apply (parse_ok_iff _ _ _ _ _ _).mpr
        rw [separated]
        exact ⟨limit, arity, texts, read, by simpa only [named] using ordered, by cases accepted; exact valid⟩
  · simp [Positional.render, emptyMarker, named, bind, Except.bind] at rendered

theorem parse_of_rendered_spelling {limits : RenderLimits} {keys : List String} {encoding : Encoding}
    {options : Options} {entries : Partition} {directory canonical : String}
    (rendered : Positional.render limits keys encoding options entries = .ok canonical)
    (fits : directory.utf8ByteSize ≤ limits.maxDirectoryBytes)
    (spelling : SameDecodedSegments encoding directory canonical) :
    parse limits.maxDirectoryBytes keys encoding options directory = .ok entries := by
  obtain ⟨_, arity, values, decoded, ordered, valid⟩ :=
    (parse_ok_iff _ _ _ _ _ _).mp (render_spec rendered).1
  exact (parse_ok_iff _ _ _ _ _ _).mpr
    ⟨fits, spelling.1.trans arity, values, spelling.2.trans decoded, ordered, valid⟩

end Silmaril.Proofs.Formats.Hive.PartitionPath.Positional
