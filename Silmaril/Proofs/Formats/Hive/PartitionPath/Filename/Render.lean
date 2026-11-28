module

public import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Defs
import Silmaril.Formats.Hive.PartitionPath.Filename.Thms
import Silmaril.Formats.Hive.PartitionPath.Positional.Thms
import Silmaril.Formats.Hive.PartitionPath.Thms
import Init.Data.String.Lemmas.Pattern.Split.Char

public section

namespace Silmaril.Proofs.Formats.Hive.PartitionPath.Filename

open Silmaril.Formats.Hive.PartitionPath
open Silmaril.Formats.Hive.PartitionPath.Filename

private theorem suffix_safe {suffix : String} (valid : safeSuffix suffix = true) :
    suffix.isEmpty = false ∧ '_' ∉ suffix.toList := by
  simp only [safeSuffix, Bool.and_eq_true] at valid
  have nonempty : suffix.isEmpty = false := by
    cases h : suffix.isEmpty
    · rfl
    · simp [h] at valid
  refine ⟨nonempty, ?_⟩
  intro hit
  have allowed := List.all_eq_true.mp valid.2 '_' hit
  contradiction

private theorem prefixTokens_intercalate (raw : List String) (suffix : String)
    (nonempty : suffix.isEmpty = false) (safe : ∀ s ∈ raw ++ [suffix], '_' ∉ s.toList) :
    prefixTokens ("_".intercalate (raw ++ [suffix])) = .ok raw := by
  have separated : (("_".intercalate (raw ++ [suffix])).split '_').toList.map String.Slice.copy =
      raw ++ [suffix] := by
    simpa using String.toList_split_intercalate safe
  unfold prefixTokens
  rw [List.map_reverse, separated]
  simp [List.reverse_append, nonempty]

private theorem renderToken_admitted {options : Options} {encoding : Positional.Encoding} {entry : Entry}
    {token : String} (rendered : renderToken options encoding entry = .ok token) :
    ∃ value, entry.2 = some value ∧ Positional.decodeSegment encoding token = .ok value ∧
      '_' ∉ token.toList := by
  obtain ⟨key, _ | value⟩ := entry
  · contradiction
  by_cases empty : value.isEmpty = true
  · simp [renderToken, empty] at rendered
  by_cases collision : value = options.nullMarker
  · subst value
    simp only [renderToken, empty, ite_false, beq_self_eq_true, ite_true, reduceCtorEq] at rendered
  cases encoding with
  | uri =>
    simp [renderToken, empty, collision] at rendered
    subst token
    have decoded := Percent.decode_encodeWith true value
    have encodedNonempty : (Percent.encodeWith true value).isEmpty = false := by
      apply Bool.eq_false_iff.mpr
      intro encodedEmpty
      rw [String.isEmpty_iff.mp encodedEmpty] at decoded
      have readEmpty : Percent.decode "" = .ok "" := by rfl
      rw [readEmpty] at decoded
      cases decoded
      contradiction
    exact ⟨value, rfl, by simp [Positional.decodeSegment, encodedNonempty, decoded],
      Percent.encodeWith_avoids_underscore value⟩
  | literal =>
    by_cases blocked : '_' ∈ value.toList ∨ '/' ∈ value.toList ∨ '\\' ∈ value.toList ∨
        ':' ∈ value.toList ∨ Char.ofNat 0 ∈ value.toList
    · simp [renderToken, empty, collision, blocked] at rendered
    · simp [renderToken, empty, collision, blocked] at rendered
      subst token
      exact ⟨value, rfl, by simp [Positional.decodeSegment, empty], fun hit => blocked (.inl hit)⟩

private theorem renderTokens_admitted {options : Options} {encoding : Positional.Encoding}
    {entries : Partition} {tokens : List String}
    (rendered : entries.mapM (renderToken options encoding) = .ok tokens) :
    tokens.length = entries.length ∧
      ∃ values, tokens.mapM (Positional.decodeSegment encoding) = .ok values ∧
        entries = (entries.map Prod.fst).zip (values.map some) ∧
          ∀ token ∈ tokens, '_' ∉ token.toList := by
  induction entries generalizing tokens with
  | nil =>
    change Except.ok [] = Except.ok tokens at rendered
    cases rendered
    exact ⟨rfl, [], rfl, rfl, by simp⟩
  | cons entry rest ih =>
    rw [List.mapM_cons] at rendered
    cases first : renderToken options encoding entry with
    | error reason => simp [first, bind, Except.bind] at rendered
    | ok token =>
      cases tail : rest.mapM (renderToken options encoding) with
      | error reason => simp [first, tail, bind, Except.bind] at rendered
      | ok tokensRest =>
        simp [first, tail, bind, Except.bind, pure, Except.pure] at rendered
        subst tokens
        obtain ⟨value, present, decoded, safe⟩ := renderToken_admitted first
        obtain ⟨lengthRest, values, decodedRest, entriesRest, safeRest⟩ := ih tail
        refine ⟨by simp [lengthRest], value :: values, ?_, ?_, ?_⟩
        · simp [List.mapM_cons, decoded, decodedRest, bind, Except.bind, pure, Except.pure]
        · simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
          exact ⟨Prod.ext rfl present, entriesRest⟩
        · intro item hit
          rcases List.mem_cons.mp hit with rfl | hit
          · exact safe
          · exact safeRest item hit

theorem parse_render_of_ok {maxFilenameBytes : Nat} {keys : List String} {encoding : Positional.Encoding}
    {options : Options} {entries : Partition} {suffix leaf : String}
    (rendered : Filename.render maxFilenameBytes keys encoding options entries suffix = .ok leaf)
    (directory : String) :
    Filename.parse maxFilenameBytes keys encoding options directory leaf = .ok entries := by
  by_cases suffixOK : safeSuffix suffix = true
  · by_cases markerEmpty : options.nullMarker.isEmpty = true
    · simp [Filename.render, suffixOK, markerEmpty] at rendered
    by_cases named : entries.map Prod.fst = keys
    · cases valid : validate options entries with
      | error reason => simp [Filename.render, suffixOK, markerEmpty, named, valid, Except.bind] at rendered
      | ok accepted =>
        cases tokenized : entries.mapM (renderToken options encoding)
        · simp [Filename.render, suffixOK, markerEmpty, named, valid, tokenized, Except.bind] at rendered
        · rename_i tokens
          simp only [Filename.render, suffixOK, markerEmpty, named, Bool.not_true,
            Bool.false_eq_true, ite_false, valid, tokenized, Except.bind] at rendered
          by_cases oversized : ("_".intercalate (tokens ++ [suffix])).utf8ByteSize > maxFilenameBytes
          · simp [oversized] at rendered
          · simp [oversized] at rendered
            subst leaf
            obtain ⟨length, values, decoded, ordered, safeTokens⟩ := renderTokens_admitted tokenized
            obtain ⟨nonempty, safeEnd⟩ := suffix_safe suffixOK
            have raw := prefixTokens_intercalate tokens suffix nonempty (by
              intro token member
              rcases List.mem_append.mp member with main | last
              · exact safeTokens token main
              · rwa [List.mem_singleton.mp last])
            have arity : tokens.length = keys.length := by
              rw [← named, List.length_map, length]
            apply (Silmaril.Formats.Hive.PartitionPath.Filename.parse_ok_iff _ _ _ _ _ _ _).mpr
            exact ⟨Nat.le_of_not_gt oversized, tokens, raw,
              (Positional.parseSegments_ok_iff _ _ _ _ _).mpr
                ⟨arity, values, decoded, by simpa only [named] using ordered, valid⟩⟩
    · simp [Filename.render, suffixOK, markerEmpty, named] at rendered
  · simp [Filename.render, suffixOK] at rendered

end Silmaril.Proofs.Formats.Hive.PartitionPath.Filename
