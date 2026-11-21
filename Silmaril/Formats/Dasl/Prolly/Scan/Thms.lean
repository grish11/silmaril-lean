module

public import Silmaril.Formats.Dasl.Prolly.Scan.Defs
import Silmaril.Proofs.Formats.Dasl.ProllyScan

public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (Block Node Policy blockOccurrences build flatten nodeBlock)

variable {Name Key Payload : Type}

theorem Read.Sound.mono {read : Read Name} {store extension : Store Name}
    (sound : Read.Sound read store) (incl : store.Subset extension) : Read.Sound read extension :=
  fun _ _ hit => incl.1 (sound hit)

theorem readBlock_sound {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    {address : Block Name Key Payload → Name} {tree : Semantics.Prolly.Tree Key Payload} {store : Store Name}
    (stored : Stored codec address tree store) (bound : store.Binding) {read : Read Name} (sound : Read.Sound read store)
    {block : Block Name Key Payload} (hit : block ∈ blockOccurrences address tree.level tree.root)
    {actual : Block Name Key Payload} (readOk : readBlock codec read (address block) = .ok actual) : actual = block :=
  Proofs.Formats.Dasl.ProllyScan.readBlock_sound stored bound sound hit readOk

theorem scan_sound [DecidableEq Key] {read : Name → Except (Fault Name) (Block Name Key Payload)}
    (address : Block Name Key Payload → Name) (width fuel level : Nat) (node : Node Key Payload level)
    (agrees : ∀ block ∈ blockOccurrences address level node,
      ∀ actual, read (address block) = .ok actual → actual = block)
    {expected : Option Nat} {entries : List (Key × Payload)}
    (checked : scan read width fuel expected (address (nodeBlock address level node)) = .ok entries) :
    entries = flatten level node :=
  Proofs.Formats.Dasl.ProllyScan.scan_sound address width fuel level node agrees checked

/-- Both positive and negative answers are correct against every binding reference
including the reader and the canonical encoding. Name uniqueness is not needed. -/
theorem lookup_sound [LinearOrder Key] {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)}
    (policy : Policy Key) {map : OrderedMap Key Payload} {address : Block Name Key Payload → Name} {store : Store Name}
    (stored : Stored codec address (build policy map) store) (bound : store.Binding) {read : Read Name}
    (sound : Read.Sound read store) {fuel : Nat} {key : Key} {result : Option Payload}
    (checked : lookup codec read policy.width fuel ((build policy map).rootName address) key = .ok result) :
    map.lookup? key = result :=
  Proofs.Formats.Dasl.ProllyScan.lookup_sound policy stored bound sound checked

end Silmaril.Formats.Dasl.Prolly
