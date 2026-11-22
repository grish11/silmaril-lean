module

public import Silmaril.ProofFormats.DaslSyntax.HOL.Defs
public import Silmaril.ProofFormats.DaslSyntax.Thms
public import Silmaril.Logic.HOLLight.Soundness.Thms
public import Silmaril.Formats.Dasl.Lift.Set.Thms
import Silmaril.Proofs.ProofFormats.DaslSyntax.HOL

public section

namespace Silmaril.ProofFormats.DaslSyntax.HOL

open Silmaril.Formats.Dasl
open Silmaril.Logic.HOLLight
open Silmaril.Semantics.Naming (Binding)

universe u

variable {Name : Type} {store : Store Name} {sig : Signature} {theory : Theory}

theorem theorems_subset_propositions : theorems store sig theory ⊆ propositions store sig :=
  tm.namesWhere_mono store (left := Derives sig theory ∅) (right := fun term => HasType sig [] term .bool)
    fun _ proof => proof.typing

theorem derives_le_entails {model : Model.{u} sig} (satisfies : Models model theory) :
    derives store sig theory ≤ entails store model :=
  system_mono (fun _ _ proof => ⟨proof.typedHyps, proof.typing, proof.sound model satisfies⟩)

theorem theorems_subset_validIn {model : Model.{u} sig} (satisfies : Models model theory) :
    theorems store sig theory ⊆ validIn store model :=
  tm.namesWhere_mono store fun _ proof =>
    ⟨proof.typing, fun types free => proof.sound model satisfies types free (by simp [HypsTrue])⟩

/-- Under binding, the two context roots have exactly the same kernel judgments when they
present the same hypothesis set. No order-insensitivity is asserted for typing contexts. -/
theorem derives_iff_derivesWith {resolved : Name → Hyps → Prop} (bound : store.Binding)
    (functional : Binding resolved) {listRoot setRoot result : Name} {premises : List Tm} {term : Tm}
    (listHit : assumptions.names store listRoot premises) (setHit : resolved setRoot premises.toFinset)
    (resultHit : tm.names store result term) : derives store sig theory listRoot result ↔
      derivesWith store resolved sig theory setRoot result :=
  Proofs.ProofFormats.DaslSyntax.HOL.system_iff_of_set (Derives sig theory) bound functional listHit setHit resultHit

theorem entails_iff_entailsWith {resolved : Name → Hyps → Prop} {model : Model.{u} sig}
    (bound : store.Binding) (functional : Binding resolved)
    {listRoot setRoot result : Name} {premises : List Tm} {term : Tm}
    (listHit : assumptions.names store listRoot premises) (setHit : resolved setRoot premises.toFinset)
    (resultHit : tm.names store result term) : entails store model listRoot result ↔
      entailsWith store resolved model setRoot result :=
  Proofs.ProofFormats.DaslSyntax.HOL.system_iff_of_set (semantic model) bound functional listHit setHit resultHit

theorem derives_iff_derivesFromSet {layout : Value → Hyps → Prop} (bound : store.Binding)
    (functional : Binding layout) {listRoot setRoot result : Name} {premises : List Tm} {term : Tm}
    (listHit : assumptions.names store listRoot premises)
    (setHit : (Lift.name store layout).represents setRoot premises.toFinset)
    (resultHit : tm.names store result term) : derives store sig theory listRoot result ↔
      derivesFromSet store layout sig theory setRoot result :=
  derives_iff_derivesWith bound (Lift.name_binding bound functional) listHit setHit resultHit

theorem entails_iff_entailsFromSet {layout : Value → Hyps → Prop} {model : Model.{u} sig}
    (bound : store.Binding) (functional : Binding layout)
    {listRoot setRoot result : Name} {premises : List Tm} {term : Tm}
    (listHit : assumptions.names store listRoot premises)
    (setHit : (Lift.name store layout).represents setRoot premises.toFinset)
    (resultHit : tm.names store result term) : entails store model listRoot result ↔
      entailsFromSet store layout model setRoot result :=
  entails_iff_entailsWith bound (Lift.name_binding bound functional) listHit setHit resultHit

end Silmaril.ProofFormats.DaslSyntax.HOL
