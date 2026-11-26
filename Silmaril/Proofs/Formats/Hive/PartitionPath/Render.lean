module

public import Silmaril.Formats.Hive.PartitionPath.Defs
import Silmaril.Proofs.Formats.Hive.PartitionPath.Correctness
import all Init.Data.String.Legacy
import Batteries.Data.String.Lemmas
import Mathlib.Data.List.TakeDrop

public section

namespace Silmaril.Proofs.Formats.Hive.PartitionPath

open Silmaril.Formats.Hive.PartitionPath
open Silmaril.Formats.Hive.PartitionPath.Percent (encode)

open String in
private theorem splitOnAux_slash (leading current remaining : List Char) (acc : List String) :
    splitOnAux (ofList (leading ++ current ++ remaining)) "/" ⟨utf8Len leading⟩
      ⟨utf8Len leading + utf8Len current⟩ 0 acc =
      acc.reverse ++ (List.splitOnPPrepend (· == '/') remaining current.reverse).map ofList := by
  induction remaining generalizing leading current acc with
  | nil =>
    unfold splitOnAux
    simp only [List.append_nil, atEnd_iff, rawEndPos_ofList, utf8Len_append, Pos.Raw.mk_le_mk,
      Nat.le_refl, ite_true, List.splitOnPPrepend_nil, List.reverse_reverse, List.map_singleton,
      ← List.reverse_cons]
    simpa using extract_of_valid leading current []
  | cons c rest ih =>
    have getChar : Pos.Raw.get (ofList (leading ++ current ++ c :: rest))
        ⟨utf8Len leading + utf8Len current⟩ = c := by
      simpa using get_of_valid (leading ++ current) (c :: rest)
    have nextChar : Pos.Raw.next (ofList (leading ++ current ++ c :: rest))
        ⟨utf8Len leading + utf8Len current⟩ =
        ⟨utf8Len leading + utf8Len current + c.utf8Size⟩ := by
      simpa using next_of_valid (leading ++ current) c rest
    have notEnd : Pos.Raw.atEnd (ofList (leading ++ current ++ c :: rest))
        ⟨utf8Len leading + utf8Len current⟩ = false := by
      apply Bool.eq_false_iff.mpr
      intro ended
      have bound := (atEnd_iff _ _).mp ended
      simp only [rawEndPos_ofList, Pos.Raw.mk_le_mk, utf8Len_append, utf8Len_cons] at bound
      have := Char.utf8Size_pos c
      omega
    have slash : Pos.Raw.get "/" 0 = '/' := by decide
    have endSlash : Pos.Raw.atEnd "/" (Pos.Raw.next "/" 0) = true := by decide
    have zeroOffset : (⟨utf8Len leading + utf8Len current⟩ : Pos.Raw).unoffsetBy 0 =
        ⟨utf8Len leading + utf8Len current⟩ := rfl
    unfold splitOnAux
    rw [notEnd, getChar, slash]
    by_cases sep : (c == '/') = true
    · have eqSlash : c = '/' := beq_iff_eq.mp sep
      subst c
      simp only [Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, endSlash, nextChar]
      have offset : (⟨utf8Len leading + utf8Len current + '/'.utf8Size⟩ : Pos.Raw).unoffsetBy
          (Pos.Raw.next "/" 0) = ⟨utf8Len leading + utf8Len current⟩ := by
        change (⟨utf8Len leading + utf8Len current + 1 - 1⟩ : Pos.Raw) = _
        simp
      rw [offset, extract_of_valid leading current ('/' :: rest)]
      simpa [List.splitOnPPrepend_cons_eq_ite, utf8Len_append, Nat.add_assoc] using
        ih (leading ++ current ++ ['/']) [] (ofList current :: acc)
    · simp only [Bool.false_eq_true, ↓reduceIte, sep, zeroOffset, nextChar]
      simpa [List.splitOnPPrepend_cons_eq_ite, sep, utf8Len_append, Nat.add_assoc] using
        ih leading (current ++ [c]) acc

open String in
private theorem splitOn_slash (value : String) :
    value.splitOn "/" = (value.toList.splitOn '/').map ofList := by
  simpa [String.splitOn, List.splitOn_eq_splitOnP,
    show ("/" == "" : Bool) = false by decide] using splitOnAux_slash [] [] value.toList []

private theorem encode_avoids (text : String) (sep : Char) (hsep : sep.toNat = 47 ∨ sep.toNat = 61) :
    sep ∉ (encode text).toList := by
  simp only [encode, String.toList_ofList, List.mem_map]
  rintro ⟨byte, hit, rfl⟩
  obtain ⟨ascii, notSlash, notEquals⟩ := Percent.escape_safe hit
  have valid : byte.toNat.isValidChar := Or.inl (by omega)
  have code : (Char.ofNat byte.toNat).toNat = byte.toNat := by
    simp [Char.toNat, Char.ofNat, valid, Char.ofNatAux]
  rw [code] at hsep
  exact hsep.elim (fun h => notSlash (UInt8.toNat.inj h)) (fun h => notEquals (UInt8.toNat.inj h))

private theorem span_equals (key value : List Char) (safe : '=' ∉ key) :
    (key ++ '=' :: value).span (· != '=') = (key, '=' :: value) := by
  have keep : ∀ c ∈ key, (c != '=') = true := by
    intro c member
    exact bne_iff_ne.mpr (fun eq => safe (eq ▸ member))
  rw [List.span_eq_takeWhile_dropWhile, List.takeWhile_append_of_pos keep, List.dropWhile_append_of_pos keep]
  simp

private theorem renderSegment_shape {options : Options} {entry : Entry} {segment : String}
    (rendered : renderSegment options entry = .ok segment) :
    segment = encode entry.1 ++ "=" ++ encode (entry.2.getD options.nullMarker) ∧
      entry.2 ≠ some options.nullMarker := by
  obtain ⟨key, value⟩ := entry
  change (if value == some options.nullMarker then Except.error (Error.nullMarkerCollision key)
    else Except.ok (encode key ++ "=" ++ encode (value.getD options.nullMarker))) = .ok segment at rendered
  by_cases collision : value = some options.nullMarker
  · simp [collision] at rendered
  · simp [collision] at rendered
    exact ⟨rendered.symm, collision⟩

private theorem segment_admitted {options : Options} {entry : Entry} {segment : String}
    (rendered : renderSegment options entry = .ok segment) (keyNonempty : entry.1.isEmpty = false) :
    parseSegment options segment = .ok entry ∧ '/' ∉ segment.toList ∧ segment ≠ "" := by
  obtain ⟨shape, noCollision⟩ := renderSegment_shape rendered
  obtain ⟨key, value⟩ := entry
  subst segment
  have chars : (encode key ++ "=" ++ encode (value.getD options.nullMarker)).toList =
      (encode key).toList ++ '=' :: (encode (value.getD options.nullMarker)).toList := by
    simp [List.append_assoc]
  have nonempty : (encode key ++ "=" ++ encode (value.getD options.nullMarker)).isEmpty = false := by simp
  have keyEquals := encode_avoids key '=' (by decide)
  have keySlash := encode_avoids key '/' (by decide)
  have valueSlash := encode_avoids (value.getD options.nullMarker) '/' (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [parseSegment, nonempty, Bool.false_eq_true, ↓reduceIte, chars,
      span_equals _ _ keyEquals, String.ofList_toList, Percent.decode_encode,
      keyNonempty, bind, Except.bind, pure, Except.pure]
    cases value <;> simp_all
  · simp [chars, keySlash, valueSlash]
  · intro empty
    rw [empty] at nonempty
    contradiction

private theorem validateKeys_nonempty {keys : List String} (valid : validateKeys keys = .ok ()) :
    ∀ key ∈ keys, key.isEmpty = false := by
  induction keys with
  | nil => simp
  | cons name rest ih =>
    unfold validateKeys at valid
    split at valid
    · cases valid
    · rename_i nonempty
      split at valid
      · cases valid
      · intro key member
        rcases List.mem_cons.mp member with rfl | member
        · exact Bool.eq_false_iff.mpr nonempty
        · exact ih valid key member

private theorem parse_renderSegments {options : Options} {entries : Partition} {segments : List String}
    (keys : ∀ entry ∈ entries, entry.1.isEmpty = false)
    (rendered : entries.mapM (renderSegment options) = .ok segments) :
    segments.mapM (parseSegment options) = .ok entries ∧
      ∀ segment ∈ segments, '/' ∉ segment.toList ∧ segment ≠ "" := by
  induction entries generalizing segments with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at rendered
    subst segments
    simp [pure, Except.pure]
  | cons entry rest ih =>
    rw [List.mapM_cons] at rendered
    cases head : renderSegment options entry with
    | error error => simp [head, bind, Except.bind] at rendered
    | ok segment =>
      cases tail : rest.mapM (renderSegment options) with
      | error error => simp [head, tail, bind, Except.bind] at rendered
      | ok more =>
        simp only [head, tail, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at rendered
        subst segments
        obtain ⟨parsed, safe⟩ := segment_admitted head (keys entry (by simp))
        obtain ⟨parsedRest, safeRest⟩ := ih (fun item member => keys item (by simp [member])) tail
        exact ⟨by simp [List.mapM_cons, parsed, parsedRest, bind, Except.bind, pure, Except.pure],
          fun item member => (List.mem_cons.mp member).elim (fun eq => eq ▸ safe) (safeRest item)⟩

theorem parse_render_of_ok {options : Options} {entries : Partition} {directory : String}
    (rendered : render options entries = .ok directory) : parse options directory = .ok entries := by
  by_cases emptyMarker : options.nullMarker.isEmpty = true
  · have stopped : render options entries = .error .emptyNullMarker := by
      simp only [render, emptyMarker, ↓reduceIte]
      rfl
    rw [stopped] at rendered
    cases rendered
  cases validated : validate options entries with
  | error error => simp [render, emptyMarker, validated, bind, Except.bind] at rendered
  | ok check =>
    cases check
    cases encoded : entries.mapM (renderSegment options) with
    | error error => simp [render, emptyMarker, validated, encoded, bind, Except.bind] at rendered
    | ok segments =>
      simp only [render, emptyMarker, Bool.false_eq_true, ↓reduceIte, validated, encoded, bind, Except.bind,
        pure, Except.pure, Except.ok.injEq] at rendered
      subst directory
      have validatedKeys : validateKeys (entries.map Prod.fst) = .ok () := by
        cases h : validateKeys (entries.map Prod.fst) with
        | error error => simp [validate, h, bind, Except.bind] at validated
        | ok accepted => cases accepted; rfl
      obtain ⟨parsed, safe⟩ := parse_renderSegments
        (fun entry member => validateKeys_nonempty validatedKeys entry.1 (List.mem_map_of_mem member)) encoded
      cases segments with
      | nil =>
        have noEntries : entries = [] := by simpa [pure, Except.pure, eq_comm] using parsed
        subst entries
        simp [parse, emptyMarker, validated, Except.bind]
      | cons first rest =>
        have separated : (String.intercalate "/" (first :: rest)).splitOn "/" = first :: rest := by
          rw [splitOn_slash, String.toList_intercalate]
          change ((['/'].intercalate ((first :: rest).map String.toList)).splitOn '/').map String.ofList = _
          rw [List.splitOn_intercalate]
          · simp
          · intro piece member
            obtain ⟨segment, included, rfl⟩ := List.mem_map.mp member
            exact (safe segment included).1
          · simp
        have nonempty : (String.intercalate "/" (first :: rest)).isEmpty = false := by
          cases rest with
          | nil => simpa [String.isEmpty_iff] using (safe first (by simp)).2
          | cons next tail => simp
        simp [parse, emptyMarker, nonempty, separated, parsed, validated, Except.bind]

end Silmaril.Proofs.Formats.Hive.PartitionPath
