module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Incoming.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Proofs

open SeaOfNodes.Diamond (Model ValueSort)
open Join (Block)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

theorem outer_suffix_bank (incoming : Bank (regs := regs) m) :
    p.outerSuffixBank m incoming = p.outerSuffix.quads.eval m incoming :=
  Prefix.compiled_bank m _ incoming

theorem inner_edges_distinct : p.innerEdgeOccurrence true ≠ p.innerEdgeOccurrence false :=
  Prefix.inner_edges_distinct p.toRoutes
    (later := p.suffix.blocks ++ p.outerFalse.blocks ++ p.outerSuffix.blocks ++ [p.join, p.latch])
    (by simpa only [List.append_assoc] using p.distinct)

theorem outer_predecessors_distinct : (p.outerEdgeOccurrence true).1 ≠ (p.outerEdgeOccurrence false).1 := by
  have ordered := p.distinct
  simp only [List.append_assoc, List.cons_append, List.nil_append] at ordered
  have fromHeader := (List.nodup_cons.mp ordered).2
  have headerAbsent := (List.nodup_cons.mp fromHeader).1
  have arms := (List.nodup_cons.mp (List.nodup_cons.mp fromHeader).2).2
  have afterTrue := (List.nodup_append.mp arms).2.1
  have suffixAndLater := (List.nodup_append.mp afterTrue).2.1
  have separate := (List.nodup_append.mp suffixAndLater).2.2
  intro samePred
  change p.suffix.predecessor p.inner = p.outerFalse.predecessor p.header at samePred
  rcases Prefix.predecessor_mem p.suffix p.inner with ⟨empty, _⟩ | yes
  · exact p.nonempty empty
  rcases Prefix.predecessor_mem p.outerFalse p.header with ⟨_, direct⟩ | no
  · have headerIn : p.header ∈ p.suffix.blocks := (samePred.trans direct) ▸ yes
    exact headerAbsent (by simp [headerIn])
  · exact separate _ yes _ (List.mem_append_left _ no) samePred

theorem outer_edges_distinct : p.outerEdgeOccurrence true ≠ p.outerEdgeOccurrence false :=
  fun equal => outer_predecessors_distinct p (congrArg Prod.fst equal)

theorem selected_outer_edge (old : Bank (regs := regs) m) :
    let occurrence := p.toControl.selected m old
    let pred := (p.outerEdgeOccurrence (occurrence != .outerFalse)).1
    let bank := (src pred).body.eval m (p.outerPredecessorBank m old occurrence)
    (src pred).terminator.select m bank = .jump p.stop ∧
      bank = p.outerBank m old occurrence := by
  let header := (src p.header).body.eval m old
  have viaInner (occurrence : Occurrence) (isInner : occurrence ≠ .outerFalse) :
      let pred := (p.outerEdgeOccurrence true).1
      let bank := (src pred).body.eval m (p.suffix.predecessorBank m header (p.toRoutes.prefixBank m old occurrence))
      (src pred).terminator.select m bank = .jump p.stop ∧ bank = p.outerBank m old occurrence := by
    have step := p.suffix.final_edge m p.inner header (p.toRoutes.prefixBank m old occurrence)
      (fun empty => (p.nonempty empty).elim)
    refine ⟨step.1, step.2.trans ?_⟩
    rw [← Prefix.suffix_bank p.toRoutes m]
    cases occurrence with
    | innerTrue => rfl
    | innerFalse => rfl
    | outerFalse => exact (isInner rfl).elim
  dsimp only
  cases selected : p.toControl.selected m old with
  | innerTrue => exact viaInner .innerTrue (by decide)
  | innerFalse => exact viaInner .innerFalse (by decide)
  | outerFalse =>
    have test : (header.get p.outerTest).down ≠ true := by
      intro yes
      have innerChosen := selected
      change (if (header.get p.outerTest).down then
          if (((src p.inner).body.eval m header).get p.innerTest).down then Occurrence.innerTrue else Occurrence.innerFalse
        else Occurrence.outerFalse) = Occurrence.outerFalse at innerChosen
      rw [ite_eq_left yes] at innerChosen
      split at innerChosen <;> cases innerChosen
    have callerEdge : (src p.header).terminator.select m header = .jump p.onOuterFalse := by
      rw [p.outerEdge, Tail.Terminator.select, ite_eq_right test]
    have step := p.outerFalse.final_edge m p.header old header (fun _ => ⟨callerEdge, rfl⟩)
    refine ⟨step.1, step.2.trans ?_⟩
    change p.outerFalse.quads.eval m header = p.toRoutes.prefixBank m old .outerFalse
    rw [Prefix.prefix_bank]
    exact List.foldl_append.symm

theorem run_outer_suffix (incoming : Bank (regs := regs) m) (fuel : Nat) :
    src.runFrom m (fuel + p.outerSuffix.blocks.length) p.stop incoming =
      src.runFrom m fuel p.join (p.outerSuffixBank m incoming) := by
  rw [p.outerSuffix.run_segment m, outer_suffix_bank]

theorem run_to_merge (old : Bank (regs := regs) m) (fuel : Nat) :
    let occurrence := p.toControl.selected m old
    src.runFrom m (fuel + p.mergeVisits occurrence) p.header old =
      src.runFrom m fuel p.join (p.mergeBank m old occurrence) := by
  dsimp only
  rw [Program.mergeVisits, ← Nat.add_assoc, Nat.add_right_comm fuel (p.outerVisits (p.toControl.selected m old)),
    Prefix.run_to_outer p.toRoutes m old (fuel + p.outerSuffix.blocks.length), run_outer_suffix]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Proofs
