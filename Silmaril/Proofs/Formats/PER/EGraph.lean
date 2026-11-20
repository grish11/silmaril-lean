module

public import Silmaril.Formats.PER.EGraph.Defs

public section

namespace Silmaril.Proofs.Formats.PER.EGraph

open Silmaril.Formats Silmaril.Formats.PER.EGraph

variable {Name : Type} {size : Nat}

theorem rawPER_eq (part : Partition size) : part.rawPER = part.per.decodePull (termId? size) := by
  apply PER.ext
  intro left right
  cases hl : termId? size left <;> cases hr : termId? size right <;>
    simp [Partition.rawPER, PER.ofDecoder, PER.decodePull, Partition.lookup, hl, hr,
      Partition.per, PER.kernel, PER.pull, PER.equality, eq_comm]

theorem signature_eq_iff (dag : Dag Name) (part : Partition dag.val.size) (left right : dag.Id) :
    dag.signature part left = dag.signature part right ↔
      dag.val[left].label = dag.val[right].label ∧ List.Forall₂ part.per.rel (dag.children left) (dag.children right) := by
  have children : List.Forall₂ part.per.rel (dag.children left) (dag.children right) ↔
      (dag.children left).map part.classOf = (dag.children right).map part.classOf := by
    change List.Forall₂ (fun a b => part.classOf a = part.classOf b) _ _ ↔ _
    rw [← List.forall₂_map_right_iff (f := part.classOf), ← List.forall₂_map_left_iff (f := part.classOf),
      List.forall₂_eq_eq_eq]
  simp only [Dag.signature, Node.mk.injEq, children]

theorem rebuilt_iff (dag : Dag Name) (part : Partition dag.val.size) :
    dag.Rebuilt part ↔ dag.Congruent part.per := by
  constructor
  · intro rebuilt left right label children
    exact rebuilt left right ((signature_eq_iff dag part left right).2 ⟨label, children⟩)
  · intro congruent left right equal
    obtain ⟨label, children⟩ := (signature_eq_iff dag part left right).1 equal
    exact congruent left right label children

theorem merge_sound {dag : Dag Name} {seeds : Seeds dag.val.size} {before after : Partition dag.val.size}
    {left right : dag.Id} {reason : Reason} (why : dag.Allows seeds before left right reason)
    (merged : before.IsMerge after left right) (sound : dag.Sound seeds before) : dag.Sound seeds after := by
  intro lhs rhs same model
  have justified : model.per.rel left right := by
    cases reason with
    | seed => exact model.asserts left right why
    | collision =>
      have sig := (signature_eq_iff dag before left right).1 why.1
      exact model.congruent left right sig.1 (sig.2.imp fun _ _ related => sound related model)
  rcases (merged lhs rhs).1 same with old | ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact sound old model
  · exact model.per.laws.trans (sound hl model) (model.per.laws.trans justified (model.per.laws.symm (sound hr model)))
  · exact model.per.laws.trans (sound hl model)
      (model.per.laws.trans (model.per.laws.symm justified) (model.per.laws.symm (sound hr model)))

end Silmaril.Proofs.Formats.PER.EGraph
