module

public import Silmaril.Parse.DecodeGraph.Defs

public section

namespace Silmaril.Parse.DecodeGraph.Proofs

open scoped SetRel

variable {Context Buffer Source Middle Target : Type*}

theorem soundFor_ofParser {Value : Type} {grammar : ByteParse.Bytes → Value → Prop}
    {parser : ByteParse.Parser Value} :
    SoundFor .byteArray (ofParser parser) (ofGrammar fun _ => grammar) ↔ ByteParse.Sound grammar parser := by
  constructor
  · intro sound bytes stop pos value endPos start bound run
    have result := sound (input := ⟨(), bytes, stop, pos⟩) (result := (value, endPos)) ⟨trivial, start, bound⟩ run
    exact ⟨result.2.1, result.2.2.1, result.2.2.2.2⟩
  · rintro sound ⟨⟨⟩, bytes, stop, pos⟩ ⟨value, endPos⟩ ⟨_, start, bound⟩ run
    obtain ⟨advance, inside, spec⟩ := sound start bound run
    exact ⟨trivial, advance, inside, bound, spec⟩

theorem completeFor_ofParser {Value : Type} {grammar : ByteParse.Bytes → Value → Prop}
    {parser : ByteParse.Parser Value} :
    CompleteFor .byteArray (ofParser parser) (ofGrammar fun _ => grammar) ↔ ByteParse.Complete grammar parser := by
  constructor
  · intro complete segment value bytes stop pos spec inside bound eqSegment
    have start : pos ≤ stop := by omega
    have encoded : grammar (ByteParse.seg bytes pos (pos + segment.length)) value := by rw [eqSegment]; exact spec
    exact complete (input := ⟨(), bytes, stop, pos⟩) (result := (value, pos + segment.length))
      ⟨trivial, start, bound⟩ ⟨trivial, Nat.le_add_right .., inside, bound, encoded⟩
  · rintro complete ⟨⟨⟩, bytes, stop, pos⟩ ⟨value, endPos⟩ _ ⟨_, advance, inside, bound, spec⟩
    change pos ≤ endPos at advance
    change endPos ≤ stop at inside
    change stop ≤ bytes.size at bound
    change grammar (ByteParse.seg bytes pos endPos) value at spec
    have endpoint : pos + (ByteParse.seg bytes pos endPos).length = endPos := by
      simp only [ByteParse.seg, List.extract_eq_take_drop, List.length_take, List.length_drop, Array.length_toList]
      change pos + min (endPos - pos) (bytes.size - pos) = endPos
      omega
    have run := complete spec (by rwa [endpoint]) bound (by rw [endpoint])
    rwa [endpoint] at run

theorem successes_deterministic {Value : Type} (run : Context → Buffer → Nat → Nat → ByteParse.Res Value) :
    Deterministic (successes run) := by
  rintro ⟨ctx, bytes, stop, pos⟩ ⟨left, leftEnd⟩ ⟨right, rightEnd⟩
    (hl : run ctx bytes stop pos = .ok left leftEnd) (hr : run ctx bytes stop pos = .ok right rightEnd)
  obtain ⟨rfl, rfl⟩ := ByteParse.Res.ok.inj (hl.symm.trans hr)
  rfl

theorem positive_ofGrammar {Value : Type} {grammar : Context → ByteParse.Bytes → Value → Prop}
    (nonempty : ∀ ctx, ByteParse.NonEmpty (grammar ctx)) : Positive (ofGrammar grammar) := by
  rintro input value endPos ⟨advance, _, _, accepted⟩
  change input.pos ≤ endPos at advance
  change grammar input.context (input.bytes.extract input.pos endPos) value at accepted
  by_cases same : endPos = input.pos
  · exact (nonempty input.context accepted (by simp [same])).elim
  · omega

theorem onSpan_comp (first : SetRel Source Middle) (second : SetRel Middle Target) :
    onSpan (first ○ second) = onSpan first ○ onSpan second := by
  ext ⟨⟨source, width⟩, ⟨target, count⟩⟩
  change ((∃ middle, source ~[first] middle ∧ middle ~[second] target) ∧ width = count) ↔
    ∃ middle : Middle × Nat,
      (source ~[first] middle.1 ∧ width = middle.2) ∧ (middle.1 ~[second] target ∧ middle.2 = count)
  constructor
  · rintro ⟨⟨middle, left, right⟩, rfl⟩
    exact ⟨(middle, width), ⟨left, rfl⟩, ⟨right, rfl⟩⟩
  · rintro ⟨⟨middle, _⟩, ⟨left, firstSpan⟩, ⟨right, secondSpan⟩⟩
    exact ⟨⟨middle, left, right⟩, firstSpan.trans secondSpan⟩

theorem transport_mono {first first' : SetRel Source Target} {graph graph' : Graph Context Buffer Source}
    (hrel : first ⊆ first') (hgraph : graph ⊆ graph') :
    transport first graph ⊆ transport first' graph' := by
  apply SetRel.comp_subset_comp hgraph
  rintro ⟨_, _⟩ ⟨related, span⟩
  exact ⟨hrel related, span⟩

theorem pointwise_comp (first : SetRel Source Middle) (second : SetRel Middle Target) :
    pointwise (first ○ second) = pointwise first ○ pointwise second := by
  ext ⟨source, target⟩
  change List.Forall₂ (fun left right => left ~[first ○ second] right) source target ↔
    ∃ middle, List.Forall₂ (fun left right => left ~[first] right) source middle ∧
      List.Forall₂ (fun left right => left ~[second] right) middle target
  constructor
  · intro aligned
    induction aligned with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons head _ ih =>
      obtain ⟨mid, left, right⟩ := SetRel.mem_comp.mp head
      obtain ⟨middle, lefts, rights⟩ := ih
      exact ⟨mid :: middle, .cons left lefts, .cons right rights⟩
  · rintro ⟨middle, lefts, rights⟩
    induction lefts generalizing target with
    | nil => cases rights; exact .nil
    | cons head _ ih =>
      cases rights with
      | cons otherHead rest => exact .cons ⟨_, head, otherHead⟩ (ih _ rest)

end Silmaril.Parse.DecodeGraph.Proofs
