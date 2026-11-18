module

public import Silmaril.Wasm.Region.ByteMap.Nested.Defs
import Silmaril.Proofs.Wasm.Region.ByteMapNested

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Nested
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

theorem located_lookup {input : Input} {seq : Sequence} (h : Located input seq) :
    Cfg.Machine.seqAt input.body seq.path = some seq.body := Proofs.located_lookup h

theorem candidate_sound {input : Input} {candidate : Candidate}
    (body : input.BodyChecks) (checked : candidate.Checks input) :
    DecodesAt input candidate.entry.decoded candidate.entry.bytes := Proofs.candidate_sound body checked

theorem entries_correct {input : Input} {candidates : List Candidate}
    (body : input.BodyChecks) (table : TableChecks input candidates) :
    ∀ m ∈ candidates.map Candidate.entry, DecodesAt input m.decoded m.bytes := Proofs.entries_correct body table

theorem entries_bounds {input : Input} {candidates : List Candidate}
    (body : input.BodyChecks) (table : TableChecks input candidates) :
    ∀ m ∈ candidates.map Candidate.entry,
      m.bytes.start < m.bytes.stop ∧ m.bytes.stop ≤ input.bytes.length := Proofs.entries_bounds body table

theorem entries_unique_decoded {input : Input} {candidates : List Candidate}
    (table : TableChecks input candidates) :
    ∀ m ∈ candidates.map Candidate.entry, ∀ n ∈ candidates.map Candidate.entry,
      m.decoded = n.decoded → m.bytes = n.bytes := Proofs.entries_unique_decoded table

theorem entries_unique_raw {input : Input} {candidates : List Candidate}
    (table : TableChecks input candidates) :
    ∀ m ∈ candidates.map Candidate.entry, ∀ n ∈ candidates.map Candidate.entry,
      m.decoded.functionIndex = n.decoded.functionIndex → m.bytes.start = n.bytes.start →
        m.decoded = n.decoded := Proofs.entries_unique_raw table

/-- Transparent construction with erased proof fields supplied through public
headers. The candidate spine is checked evidence, not part of the output map. -/
def certify (input : Input) (candidates : List Candidate)
    (body : input.BodyChecks) (table : TableChecks input candidates) : Certified input :=
  ⟨body_encoding input [] body ⟨by simp, by simp, by simp⟩,
    ⟨candidates.map Candidate.entry, entries_correct body table, entries_bounds body table,
      entries_unique_decoded table, entries_unique_raw table⟩⟩

def validate? (input : Input) (candidates : List Candidate) : Option (Certified input) :=
  if body : input.BodyChecks then
    if table : TableChecks input candidates then some (certify input candidates body table)
    else none
  else none

theorem validate_certify {input : Input} {candidates : List Candidate}
    (body : input.BodyChecks) (table : TableChecks input candidates) :
    validate? input candidates = some (certify input candidates body table) := by
  simp only [validate?, dite_eq_left body, dite_eq_left table]

theorem validate_entries {input : Input} {candidates : List Candidate} {result : Certified input}
    (h : validate? input candidates = some result) : result.map.entries = candidates.map Candidate.entry := by
  unfold validate? at h
  split at h <;> try contradiction
  split at h <;> cases h; rfl

/-- Explicit coverage over a supplied decoded inventory. Empty/partial tables
are allowed, but provide no coverage of omitted nested instructions. -/
def Covered (labels : List DecodedLabel) (candidates : List Candidate) : Prop :=
  ∀ label ∈ labels, ∃ c ∈ candidates, c.entry.decoded = label

instance (labels : List DecodedLabel) (candidates : List Candidate) : Decidable (Covered labels candidates) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

theorem inventory_member {input : Input} {b : Cfg.BlockId} {sg : Cfg.Segment}
    {body : Silmaril.Wasm.Expr} (member : (b, sg) ∈ Cfg.blocks input.body)
    (lookup : Cfg.Machine.seqAt input.body b.seq = some body) (k : Fin body.length) :
    (⟨input.functionIndex, b.seq, k.val⟩ : DecodedLabel) ∈ inventory input :=
  Proofs.inventory_member member lookup k

theorem coverage_sound {input : Input} {candidates : List Candidate} {result : Certified input}
    {labels : List DecodedLabel} (validated : validate? input candidates = some result)
    (coverage : Covered labels candidates) (label : DecodedLabel) (member : label ∈ labels) :
    ∃ m ∈ result.map.entries, m.decoded = label ∧ DecodesAt input label m.bytes := by
  obtain ⟨c, hc, eq⟩ := coverage label member
  have inMap : c.entry ∈ result.map.entries := by rw [validate_entries validated]; exact List.mem_map.mpr ⟨c, hc, rfl⟩
  exact ⟨c.entry, inMap, eq, eq ▸ result.map.correct c.entry inMap⟩

/-- Full coverage of the reused CFG inventory supplies a validated byte row
for every instruction of every sequence named by an actual extracted block. -/
theorem cfg_coverage_sound {input : Input} {candidates : List Candidate} {result : Certified input}
    (validated : validate? input candidates = some result)
    (coverage : Covered (inventory input) candidates) {b : Cfg.BlockId} {sg : Cfg.Segment}
    {body : Silmaril.Wasm.Expr} (member : (b, sg) ∈ Cfg.blocks input.body)
    (lookup : Cfg.Machine.seqAt input.body b.seq = some body) (k : Fin body.length) :
    ∃ m ∈ result.map.entries, m.decoded = ⟨input.functionIndex, b.seq, k.val⟩ ∧
      DecodesAt input ⟨input.functionIndex, b.seq, k.val⟩ m.bytes :=
  coverage_sound validated coverage _ (inventory_member member lookup k)

end Silmaril.Wasm.Region.ByteMap.Nested
