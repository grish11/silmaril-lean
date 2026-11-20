module

public import Silmaril.Formats.PER.EGraph.Defs
import Silmaril.Proofs.Formats.PER.EGraph

public section

namespace Silmaril.Formats.PER.EGraph

variable {Name : Type} {size : Nat}

theorem Dag.children_wf (dag : Dag Name) :
    WellFounded (fun child parent : dag.Id => child.val ∈ dag.val[parent].children) :=
  Subrelation.wf (fun {_ parent} member => dag.property parent _ member) (measure Fin.val).wf

theorem Partition.rawPER_eq (part : Partition size) : part.rawPER = part.per.decodePull (termId? size) :=
  Proofs.Formats.PER.EGraph.rawPER_eq part

theorem Dag.signature_eq_iff (dag : Dag Name) (part : Partition dag.val.size) (left right : dag.Id) :
    dag.signature part left = dag.signature part right ↔
      dag.val[left].label = dag.val[right].label ∧ List.Forall₂ part.per.rel (dag.children left) (dag.children right) :=
  Proofs.Formats.PER.EGraph.signature_eq_iff dag part left right

theorem Dag.rebuilt_iff (dag : Dag Name) (part : Partition dag.val.size) :
    dag.Rebuilt part ↔ dag.Congruent part.per :=
  Proofs.Formats.PER.EGraph.rebuilt_iff dag part

theorem Dag.generated_model (dag : Dag Name) (seeds : Seeds dag.val.size) :
    ∃ model : Model dag seeds, model.per = dag.generated seeds :=
  ⟨⟨dag.generated seeds, fun id model => model.reflexive id,
      fun left right seed model => model.asserts left right seed,
      fun left right label children model => model.congruent left right label
        (children.imp fun _ _ justified => justified model)⟩, rfl⟩

theorem Dag.sound_of_injective (dag : Dag Name) (seeds : Seeds dag.val.size) (part : Partition dag.val.size)
    (discrete : Function.Injective part.classOf) : dag.Sound seeds part := by
  intro left right same model
  exact (discrete same) ▸ model.reflexive left

/-- A completed sound snapshot is exact for the observed diagram if it also
contains the seeds. Shape validity or a rebuilt table alone is insufficient. -/
theorem Dag.exact_of_rebuilt {dag : Dag Name} {seeds : Seeds dag.val.size} {part : Partition dag.val.size}
    (sound : dag.Sound seeds part) (rebuilt : dag.Rebuilt part)
    (asserts : ∀ left right, seeds left right = true → part.per.rel left right) :
    part.rawPER = (dag.generated seeds).decodePull (termId? dag.val.size) := by
  rw [part.rawPER_eq]
  congr 1
  exact PER.ext fun _ _ => ⟨fun related => sound related,
    fun generated => generated ⟨part.per, fun _ => rfl, asserts, (dag.rebuilt_iff part).1 rebuilt⟩⟩

theorem Dag.merge_sound {dag : Dag Name} {seeds : Seeds dag.val.size} {before after : Partition dag.val.size}
    {left right : dag.Id} {reason : Reason} (why : dag.Allows seeds before left right reason)
    (merged : before.IsMerge after left right) (sound : dag.Sound seeds before) : dag.Sound seeds after :=
  Proofs.Formats.PER.EGraph.merge_sound why merged sound

theorem Dag.merge_isSome [DecidableEq Name] (dag : Dag Name) (seeds : Seeds dag.val.size)
    (before after : Partition dag.val.size) (left right : dag.Id) (reason : Reason) :
    (dag.merge? seeds before after left right reason).isSome = true ↔
      dag.Allows seeds before left right reason ∧ before.IsMerge after left right := by
  unfold Dag.merge?; split <;> simp_all

theorem Dag.checked_merge_sound [DecidableEq Name] {dag : Dag Name} {seeds : Seeds dag.val.size}
    {before after : Partition dag.val.size} {left right : dag.Id} {reason : Reason}
    (accepted : (dag.merge? seeds before after left right reason).isSome = true)
    (sound : dag.Sound seeds before) : dag.Sound seeds after := by
  have checked := (dag.merge_isSome seeds before after left right reason).1 accepted
  exact Dag.merge_sound checked.1 checked.2 sound

end Silmaril.Formats.PER.EGraph
