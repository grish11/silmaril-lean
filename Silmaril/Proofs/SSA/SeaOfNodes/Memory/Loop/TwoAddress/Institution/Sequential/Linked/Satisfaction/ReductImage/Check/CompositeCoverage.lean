module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Lift

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs

open CategoryTheory
open RVSDG (Port)
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q R : EntrySignature}

theorem checkInjectiveOnImage_iff (h : P ⟶ Q) (k : Q ⟶ R) (sort : ValueSort) :
    checkInjectiveOnImage h k sort = true ↔
      Set.InjOn (fun port : Port Q.args sort => k.port port) (Set.range (fun port : Port P.args sort => h.port port)) := by
  have image (port : Port Q.args sort) :
      port ∈ (portsOf sort P.args).map (fun p => h.port p) ↔
        port ∈ Set.range (fun p : Port P.args sort => h.port p) :=
    ⟨fun mem => (List.mem_map.mp mem).imp fun _ proof => proof.2,
      fun ⟨p, equal⟩ => List.mem_map.mpr ⟨p, portsOf_complete p, equal⟩⟩
  simp only [checkInjectiveOnImage, List.all_eq_true, decide_eq_true_eq, slot_eq_iff, image, Set.InjOn]

theorem checkNoIdentification_comp (h : P ⟶ Q) (k : Q ⟶ R) (sort : ValueSort) :
    checkNoIdentification (h ≫ k) sort = (checkNoIdentification h sort && checkInjectiveOnImage h k sort) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true_iff, checkNoIdentification_iff, checkNoIdentification_iff, checkInjectiveOnImage_iff]
  change Function.Injective (fun port : Port P.args sort => k.port (h.port port)) ↔ _
  constructor
  · intro composite
    refine ⟨?_, ?_⟩
    · intro left right same
      exact composite (congrArg (fun p => k.port p) same)
    · rintro _ ⟨left, rfl⟩ _ ⟨right, rfl⟩ same
      exact congrArg (fun p => h.port p) (composite same)
  · rintro ⟨first, second⟩ _ _ same
    exact first (second ⟨_, rfl⟩ ⟨_, rfl⟩ same)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Proofs
