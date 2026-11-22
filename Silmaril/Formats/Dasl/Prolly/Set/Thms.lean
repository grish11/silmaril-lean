module

public import Silmaril.Formats.Dasl.Prolly.Set.Defs
public import Silmaril.Formats.Dasl.Prolly.Scan.Thms

public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics (OrderedSet)
open Silmaril.Semantics.Prolly (Block Policy build)
open Silmaril.Semantics.Naming (Binding)

variable {Name Key : Type} [LinearOrder Key]

theorem setNames_binding (codec : Encode.PartialCodec (Block Name Key Unit) (Shallow Name))
    (read : Read Name) (width fuel : Nat) : Binding (setNames codec read width fuel) :=
  fun _ _ _ ⟨_, first, left⟩ ⟨_, second, right⟩ =>
    left.symm.trans (Except.ok.inj (first.symm.trans second) ▸ right)

theorem not_setNames_of_error {codec : Encode.PartialCodec (Block Name Key Unit) (Shallow Name)}
    {read : Read Name} {width fuel : Nat} {root : Name} {fault : Fault Name} {keys : Finset Key}
    (failed : closedSet codec read width fuel root = .error fault) : ¬ setNames codec read width fuel root keys := by
  rintro ⟨_, checked, _⟩
  cases failed.symm.trans checked

theorem setNames_sound {codec : Encode.PartialCodec (Block Name Key Unit) (Shallow Name)} (policy : Policy Key)
    {set : OrderedSet Key} {address : Block Name Key Unit → Name} {store : Store Name}
    (stored : Stored codec address (build policy set) store) (bound : store.Binding)
    {read : Read Name} (sound : Read.Sound read store) {fuel : Nat} {keys : Finset Key}
    (matched : setNames codec read policy.width fuel ((build policy set).rootName address) keys) :
    set.keys.toFinset = keys :=
  let ⟨_, checked, identified⟩ := matched
  closedMap_sound policy stored bound sound checked ▸ identified

end Silmaril.Formats.Dasl.Prolly
