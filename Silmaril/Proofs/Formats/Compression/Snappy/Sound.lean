module

public import Silmaril.Formats.Compression.Snappy.Defs

public section

namespace Silmaril.Proofs.Formats.Compression.Snappy

open Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Snappy
open Silmaril.Formats.Compression.Snappy.Internal

private theorem readBody_size {head : TagHead} {input rest : List UInt8} {tag : Tag}
    (h : head.readBody input = .ok (tag, rest)) : tag.size = head.size := by
  cases head with
  | literal length =>
    simp only [TagHead.readBody, takeBytes, List.splitAt_eq] at h
    split at h
    · next size =>
      cases h
      exact size
    · simp [bind, Except.bind] at h
  | copy offset length =>
    cases h
    rfl

private theorem tagsSize_cons (tag : Tag) (tags : List Tag) :
    tagsSize (tag :: tags) = tag.size + tagsSize tags := rfl

theorem readTags_size {fuel room : Nat} {input rest : List UInt8} {rev tags : List Tag}
    (h : readTags fuel room input rev = .ok (tags, rest)) :
    tagsSize tags = tagsSize rev + room := by
  induction fuel generalizing room input rev with
  | zero =>
    cases room with
    | zero => cases h; simp [tagsSize]
    | succ room => cases h
  | succ fuel ih =>
    cases room with
    | zero => cases h; simp [tagsSize]
    | succ room =>
      cases hdr : readTagHead input with
      | error error => simp [readTags, hdr, bind, Except.bind] at h
      | ok pair =>
        obtain ⟨head, tail⟩ := pair
        simp only [readTags, hdr, bind, Except.bind] at h
        split at h
        · simp [throw] at h
        · next fits =>
          cases payload : head.readBody tail with
          | error error => simp [payload] at h
          | ok result =>
            obtain ⟨tag, unread⟩ := result
            simp only [payload] at h
            have declared := ih h
            rw [tagsSize_cons, readBody_size payload] at declared
            omega

theorem parseMember_bounds {limit : Nat} {input rest : List UInt8} {block : Block}
    (h : parseMember limit input = .ok (block, rest)) :
    tagsSize block.tags = block.length ∧ block.length ≤ limit := by
  unfold parseMember at h
  split at h
  · simp [throw, bind, Except.bind] at h
  · cases preamble : readLength 5 input with
    | error error => simp [preamble, bind, Except.bind] at h
    | ok result =>
      obtain ⟨size, tail⟩ := result
      simp only [preamble, pure, Except.pure, bind, Except.bind] at h
      split at h
      · simp [throw] at h
      · next bounded =>
        cases tagsEq : readTags size size tail [] with
        | error error => simp [tagsEq] at h
        | ok result =>
          obtain ⟨tags, unread⟩ := result
          simp only [tagsEq] at h
          cases h
          constructor
          · simpa [tagsSize] using readTags_size tagsEq
          · exact Nat.le_of_not_gt bounded

theorem parse_eq_ok_iff {limit : Nat} {input : List UInt8} {block : Block} :
    parse limit input = .ok block ↔ parseMember limit input = .ok (block, []) := by
  unfold parse
  cases member : parseMember limit input with
  | error error => simp [bind, Except.bind]
  | ok result =>
    obtain ⟨parsed, rest⟩ := result
    cases rest <;> simp [bind, Except.bind]

private theorem copyBack_length (offset count : Nat) (history : List UInt8) :
    (Deflate.copyBack offset history count).length = history.length + count := by
  induction count generalizing history with
  | zero => rfl
  | succ count ih => simp [Deflate.copyBack, ih, Nat.add_comm, Nat.add_left_comm]

theorem denotes_length {history out : List UInt8} {tags : List Tag}
    (h : Denotes history tags out) : out.length = history.length + tagsSize tags := by
  induction h with
  | nil => rfl
  | @cons history next _ tag tags step _ ih =>
    have lengthEq : next.length = history.length + tag.size := by
      cases step with
      | literal bytes => simp [Tag.size]
      | copy length positive within => simp [Tag.size, copyBack_length]
    rw [ih, lengthEq, tagsSize_cons, Nat.add_assoc]

private theorem applyTag_sound {history out : Array UInt8} {tag : Tag}
    (h : applyTag history tag = .ok out) : tag.Denotes history.toList out.toList := by
  cases tag with
  | literal bytes =>
    cases h
    simpa using (Tag.Denotes.literal (history := history.toList) bytes)
  | copy offset length =>
    simp only [applyTag] at h
    split at h
    · next valid =>
      cases h
      rw [Deflate.copyBackArr_toList]
      exact .copy length valid.1 (by simpa using valid.2)
    · cases h

theorem expandTags_sound {history out : Array UInt8} {tags : List Tag}
    (h : expandTags history tags = .ok out) : Denotes history.toList tags out.toList := by
  induction tags generalizing history with
  | nil => cases h; exact .nil _
  | cons tag tags ih =>
    cases step : applyTag history tag with
    | error error => simp [expandTags, step, bind, Except.bind] at h
    | ok next =>
      simp only [expandTags, step, bind, Except.bind] at h
      exact .cons (applyTag_sound step) (ih h)

theorem decode_sound {limit : Nat} {input out : List UInt8} (h : decode limit input = .ok out) :
    ∃ block, parseMember limit input = .ok (block, []) ∧ Denotes [] block.tags out ∧
      out.length = block.length ∧ block.length ≤ limit := by
  cases parsed : parse limit input with
  | error error => simp [decode, parsed, bind, Except.bind] at h
  | ok block =>
    simp only [decode, parsed, bind, Except.bind] at h
    cases expanded : expandTags #[] block.tags with
    | error error => simp [expanded] at h
    | ok expandedOut =>
      simp only [expanded, pure, Except.pure] at h
      cases h
      have member := parse_eq_ok_iff.mp parsed
      have meaning := expandTags_sound expanded
      have bounds := parseMember_bounds member
      have outputSize : expandedOut.toList.length = tagsSize block.tags := by
        simpa using denotes_length meaning
      exact ⟨block, member, meaning, outputSize.trans bounds.1, bounds.2⟩

end Silmaril.Proofs.Formats.Compression.Snappy
