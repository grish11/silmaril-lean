module

public import Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Assumptions.Defs
public import Silmaril.ProofFormats.DaslSyntax.HOL.Thms
import Silmaril.Formats.Dasl.Prolly.Set.Thms
import Silmaril.Proofs.ProofFormats.DaslSyntax.HOL.Prolly.Assumptions

public section

namespace Silmaril.ProofFormats.DaslSyntax.HOL.Prolly

open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.Prolly (Read Stored ByteKey setNames_binding setNames_sound)
open Silmaril.Logic.HOLLight
open Silmaril.Semantics (OrderedSet)
open Silmaril.Semantics.Naming (Binding)
open Silmaril.Semantics.Prolly (Block Policy build)

universe u

variable {Name : Type} {store : Store Name} {read : Read Name} {width fuel : Nat}
variable {sig : Signature} {theory : Theory} {listRoot setRoot result : Name} {premises : List Tm} {term : Tm}

local instance : DecidableEq ByteKey := (inferInstance : LinearOrder ByteKey).toDecidableEq

theorem assumptions_binding (read : Read Name) (width fuel : Nat) : Binding (assumptions read width fuel) :=
  Lift.codedSet_binding (setNames_binding assumptionCodec read width fuel) hypothesisKey

theorem assumptions_iff_read {hyps : Hyps} : assumptions read width fuel setRoot hyps ↔
    ∃ terms, readAssumptions read width fuel setRoot = .ok terms ∧ terms.toFinset = hyps :=
  Proofs.ProofFormats.DaslSyntax.HOL.Prolly.assumptions_iff_read

/-- A failed scan supplies no finite expansion. This does not refute any HOL judgment
about the assumptions a complete reader might obtain. -/
theorem no_assumptions_of_error {fault : ReadFault Name}
    (failed : readAssumptions read width fuel setRoot = .error fault) :
    ¬ ∃ hyps, assumptions read width fuel setRoot hyps := by
  rintro ⟨_, matchSet⟩
  obtain ⟨_, checked, _⟩ := assumptions_iff_read.mp matchSet
  cases failed.symm.trans checked

/-- A read of a stored canonical build can only recover the corresponding hypotheses.
The hypotheses on the reader and store do not promise that it finds every block. -/
theorem assumptions_sound (policy : Policy ByteKey) {keys : OrderedSet ByteKey} {hyps : Hyps}
    {address : Block Name ByteKey Unit → Name} (stored : Stored assumptionCodec address (build policy keys) store)
    (bound : store.Binding) (sound : Read.Sound read store)
    (hit : assumptions read policy.width fuel ((build policy keys).rootName address) hyps) :
    keys.keys.toFinset = hyps.image hypothesisKey.encode :=
  setNames_sound policy stored bound sound hit

theorem derives_iff_kernel (bound : store.Binding) (hit : readAssumptions read width fuel setRoot = .ok premises)
    (resultHit : tm.names store result term) :
    derives store read width fuel sig theory setRoot result ↔ Derives sig theory premises.toFinset term :=
  system_of_match (assumptions_binding read width fuel) (tm.named_binding bound)
    (assumptions_iff_read.mpr ⟨premises, hit, rfl⟩) resultHit

theorem entails_iff_semantic {model : Model.{u} sig} (bound : store.Binding)
    (hit : readAssumptions read width fuel setRoot = .ok premises) (resultHit : tm.names store result term) :
    entails store read width fuel model setRoot result ↔ semantic model premises.toFinset term :=
  system_of_match (assumptions_binding read width fuel) (tm.named_binding bound)
    (assumptions_iff_read.mpr ⟨premises, hit, rfl⟩) resultHit

theorem derives_iff_list (bound : store.Binding) {listed : List Tm}
    (listHit : HOL.assumptions.names store listRoot listed) (hit : readAssumptions read width fuel setRoot = .ok premises)
    (same : premises.toFinset = listed.toFinset) (resultHit : tm.names store result term) :
    HOL.derives store sig theory listRoot result ↔ derives store read width fuel sig theory setRoot result :=
  HOL.derives_iff_derivesWith bound (assumptions_binding read width fuel) listHit
    (assumptions_iff_read.mpr ⟨premises, hit, same⟩) resultHit

theorem entails_iff_list {model : Model.{u} sig} (bound : store.Binding) {listed : List Tm}
    (listHit : HOL.assumptions.names store listRoot listed) (hit : readAssumptions read width fuel setRoot = .ok premises)
    (same : premises.toFinset = listed.toFinset) (resultHit : tm.names store result term) :
    HOL.entails store model listRoot result ↔ entails store read width fuel model setRoot result :=
  HOL.entails_iff_entailsWith bound (assumptions_binding read width fuel) listHit
    (assumptions_iff_read.mpr ⟨premises, hit, same⟩) resultHit

end Silmaril.ProofFormats.DaslSyntax.HOL.Prolly
