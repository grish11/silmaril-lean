module

public import Silmaril.Wasm.Region.ByteMap.Nested.Defs

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Nested.Proofs
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

theorem located_bounds {input : Input} {seq : Sequence} (h : Located input seq) :
    input.codeStart ≤ seq.span.start ∧ seq.span.stop ≤ input.bytes.length := by
  cases h with
  | root body => exact ⟨le_rfl, max_le body.1 (Nat.sub_le _ _)⟩
  | child _ encoded _ _ _ => exact ⟨encoded.1, encoded.2.1⟩

theorem located_lookup {input : Input} {seq : Sequence} (h : Located input seq) :
    Cfg.Machine.seqAt input.body seq.path = some seq.body := by
  cases h with
  | root => rfl
  | child _ encoded _ _ _ => exact encoded.2.2.1

theorem follow_sound {input : Input} {parent result : Sequence} {spine : List Frame}
    (ancestor : Located input parent) (h : follow? input parent spine = some result) : Located input result := by
  induction spine generalizing parent with
  | nil => cases h; exact ancestor
  | cons f rest ih =>
    simp only [follow?] at h
    split at h
    · rename_i checked
      cases selected : f.child? parent with
      | none => simp [selected] at h
      | some child =>
        simp only [selected] at h
        dsimp only [Bind.bind, Option.bind] at h
        split at h
        · rename_i enc
          exact ih (.child ancestor ⟨enc.1, enc.2.1, enc.2.2.1, sequence_encoding enc.2.2.2⟩ f checked selected) h
        · contradiction
    · contradiction

theorem candidate_sound {input : Input} {candidate : Candidate}
    (body : input.BodyChecks) (checked : candidate.Checks input) :
    DecodesAt input candidate.entry.decoded candidate.entry.bytes := by
  obtain ⟨seq, member, fn, path, checks⟩ := checked
  have followed : follow? input (root input) candidate.spine = some seq := by
    simpa only [Option.mem_toList] using member
  have located := follow_sound (.root body) followed
  obtain ⟨start, nonempty, stop, prefixEncoding, hasInstr, instrEncoding⟩ := checks
  have bounds := located_bounds located
  refine ⟨seq, located, fn, path, bounds.1.trans start, nonempty, stop.trans bounds.2,
    sequence_encoding prefixEncoding, ?_⟩
  cases hi : seq.body[candidate.entry.decoded.instructionOffset]? with
  | none => simp [hi] at hasInstr
  | some instr => exact ⟨instr, rfl, instruction_encoding (by simpa [hi] using instrEncoding)⟩

theorem inventory_member {input : Input} {b : Cfg.BlockId} {sg : Cfg.Segment}
    {body : Silmaril.Wasm.Expr} (member : (b, sg) ∈ Cfg.blocks input.body)
    (lookup : Cfg.Machine.seqAt input.body b.seq = some body) (k : Fin body.length) :
    (⟨input.functionIndex, b.seq, k.val⟩ : DecodedLabel) ∈ inventory input := by
  apply List.mem_flatMap.mpr
  refine ⟨(b, sg), member, ?_⟩
  simp only [lookup]
  exact List.mem_map.mpr ⟨k.val, List.mem_range.mpr k.isLt, rfl⟩

theorem entries_correct {input : Input} {candidates : List Candidate}
    (body : input.BodyChecks) (table : TableChecks input candidates) :
    ∀ m ∈ candidates.map Candidate.entry, DecodesAt input m.decoded m.bytes := by
  intro m hm
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  exact candidate_sound body (table.1 c hc)

theorem entries_bounds {input : Input} {candidates : List Candidate}
    (body : input.BodyChecks) (table : TableChecks input candidates) :
    ∀ m ∈ candidates.map Candidate.entry,
      m.bytes.start < m.bytes.stop ∧ m.bytes.stop ≤ input.bytes.length := by
  intro m hm
  obtain ⟨_, _, _, _, _, nonempty, bounded, _⟩ := entries_correct body table m hm
  exact ⟨nonempty, bounded⟩

theorem entries_unique_decoded {input : Input} {candidates : List Candidate}
    (table : TableChecks input candidates) :
    ∀ m ∈ candidates.map Candidate.entry, ∀ n ∈ candidates.map Candidate.entry,
      m.decoded = n.decoded → m.bytes = n.bytes := by
  intro m hm n hn same
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hn
  exact table.2.1 c hc d hd same

theorem entries_unique_raw {input : Input} {candidates : List Candidate}
    (table : TableChecks input candidates) :
    ∀ m ∈ candidates.map Candidate.entry, ∀ n ∈ candidates.map Candidate.entry,
      m.decoded.functionIndex = n.decoded.functionIndex → m.bytes.start = n.bytes.start →
        m.decoded = n.decoded := by
  intro m hm n hn fn start
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hn
  exact table.2.2 c hc d hd fn start

end Silmaril.Wasm.Region.ByteMap.Nested.Proofs
