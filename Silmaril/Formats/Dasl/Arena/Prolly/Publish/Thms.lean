module

public import Silmaril.Formats.Dasl.Arena.Prolly.Publish.Defs
import Silmaril.Formats.Dasl.Arena.Prolly.Index.Thms
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Publish

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Publish

open Silmaril.Formats.Dasl.Prolly (RootProfile)
open Silmaril.Semantics.Naming (collisions graph listed union)

variable {Name Key Payload : Type} {profile : RootProfile Name Key Payload}

theorem stage_name (arena : Indexed Name Key Payload) (fuel : Nat) (ref : Handle Name) :
    (stage arena profile fuel ref).map Plan.root = arena.name? profile.nameBlock? fuel ref :=
  Proofs.Formats.Dasl.Arena.Prolly.Publish.stage_name arena fuel ref

theorem stage_root_packed (arena : Indexed Name Key Payload) {fuel index : Nat} {plan : Plan profile}
    (staged : stage arena profile fuel (.local index) = some plan) :
    ∃ packed ∈ plan.blocks, packed.name = plan.root :=
  Proofs.Formats.Dasl.Arena.Prolly.Publish.stage_root_packed arena staged

theorem eager_stage (arena : Indexed Name Key Payload) (fuel : Nat) (index : Fin arena.blocks.size) :
    (arena.eagerNames profile.nameBlock? fuel)[index.val]? =
      some ((stage arena profile fuel (.local index)).map Plan.root) := by
  rw [Indexed.eagerNames_at, stage_name]

theorem Packed.readback (reader : profile.Readback) (packed : Packed profile) {read : Name → Option ByteArray}
    (present : read packed.name = some packed.bytes) : reader.readBlock? read packed.name = some packed.block :=
  Proofs.Formats.Dasl.Arena.Prolly.Publish.packed_readback reader packed present

/-- After naming, publication either extends the authoritative snapshot by
exactly the planned bytes or witnesses a conflicting name in the union. Even
prior malformed bytes are preserved; no hash injectivity is used. -/
theorem publish_spec [DecidableEq Name] (arena : Indexed Name Key Payload) (reader : profile.Readback)
    (read : Name → Option ByteArray) {fuel index : Nat} {plan : Plan profile}
    (staged : stage arena profile fuel (.local index) = some plan) :
    match publish arena profile fuel index read with
    | .ok (name, updated) => name = plan.root ∧ graph updated = union (graph read) (listed plan.writes) ∧
        ∀ packed ∈ plan.blocks, reader.readBlock? updated packed.name = some packed.block
    | .error (.collision name) => name ∈ collisions (union (graph read) (listed plan.writes))
    | .error .naming => False :=
  Proofs.Formats.Dasl.Arena.Prolly.Publish.publish_spec arena reader read staged

end Silmaril.Formats.Dasl.Arena.Prolly.Publish
