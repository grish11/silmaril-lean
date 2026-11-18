module

public import Silmaril.Machine.DecodeGraph.Defs

public section

namespace Silmaril.Machine.DecodeGraph.Proofs

open scoped SetRel

variable {Context Source Middle Target : Type*}

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

theorem transport_mono {first first' : SetRel Source Target} {graph graph' : Graph Context Source}
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

theorem blocks_mono {first second : Graph (Context × Nat) Source}
    (h : first ⊆ second) (ends : Context → Nat → Source → Prop) (fuel : Nat) :
    blocks first ends fuel ⊆ blocks second ends fuel := by
  rintro ⟨⟨⟨ctx, addr⟩, bytes⟩, code, span⟩ (path : Path first ends fuel ctx addr bytes code span)
  show Path second ends fuel ctx addr bytes code span
  induction path with
  | last decoded positive fits stop => exact .last (h decoded) positive fits stop
  | next decoded positive fits continue_ _ ih => exact .next (h decoded) positive fits continue_ ih

theorem path_bounds {decoder : Graph (Context × Nat) Source} {ends : Context → Nat → Source → Prop}
    {fuel ctx addr bytes code span} (path : Path decoder ends fuel ctx addr bytes code span) :
    0 < code.length ∧ code.length ≤ fuel ∧ code.length ≤ span ∧ span ≤ bytes.length := by
  induction path with
  | last _ positive fits _ =>
    simp only [List.length_singleton]
    omega
  | next _ positive fits _ _ ih =>
    obtain ⟨_, fuelBound, spanBound, bytesBound⟩ := ih
    simp only [List.length_cons, List.length_drop] at *
    omega

theorem blocks_deterministic {decoder : Graph (Context × Nat) Source} (unique : Deterministic decoder)
    (ends : Context → Nat → Source → Prop) (fuel : Nat) : Deterministic (blocks decoder ends fuel) := by
  rintro ⟨⟨ctx, addr⟩, bytes⟩ ⟨code, span⟩ ⟨otherCode, otherSpan⟩
    (first : Path decoder ends fuel ctx addr bytes code span)
    (second : Path decoder ends fuel ctx addr bytes otherCode otherSpan)
  induction first generalizing otherCode otherSpan with
  | last decoded _ _ stop =>
    cases second with
    | last decoded' =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (unique decoded decoded')
      rfl
    | next decoded' _ _ continues =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (unique decoded decoded')
      exact (continues stop).elim
  | next decoded _ _ continues _ ih =>
    cases second with
    | last decoded' _ _ stop =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (unique decoded decoded')
      exact (continues stop).elim
    | next decoded' _ _ _ tail =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (unique decoded decoded')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ih _ _ tail)
      rfl

theorem dom_rebase_of_covered {Input Base Observation : Type*} (adapter : SetRel Input Base)
    (machine : Observed Base Observation) (available : adapter.cod ⊆ machine.dom) :
    (rebase adapter machine).dom = adapter.dom := by
  ext input
  constructor
  · rintro ⟨obs, base, related, _⟩
    exact ⟨base, related⟩
  · rintro ⟨base, related⟩
    obtain ⟨obs, observed⟩ := available ⟨input, related⟩
    exact ⟨obs, base, related, observed⟩

end Silmaril.Machine.DecodeGraph.Proofs
