module

public import Silmaril.Formats.Dasl.Arena.Prolly.Defs
public import Silmaril.Formats.Dasl.Prolly.Route.Thms
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly

open Silmaril.Formats.Dasl.Prolly (Fault Read Stored PathReads readBlock routedLookup routedLookup_sound routedLookup_complete)
open Silmaril.Semantics.Prolly (Block)

variable {Name Key Payload : Type}

theorem readRaw_sound (decoder : RawStore.Decoder Name) [DecidablePred decoder.objectName]
    {fetch : Name → Option ByteArray} {raw : RawStore.Blocks Name}
    (sound : ∀ ⦃name bytes⦄, fetch name = some bytes → raw name bytes) :
    Read.Sound (readRaw decoder fetch) (decoder.view raw) :=
  Proofs.Formats.Dasl.Arena.Prolly.readRaw_sound decoder sound

theorem restrict_sound [DecidableEq Name] {input : Read Name} {store : Store Name}
    (sound : Read.Sound input store) (names : List Name) : Read.Sound (restrict input names) store := by
  intro name value hit
  by_cases acquired : name ∈ names <;> simp [restrict, acquired] at hit
  exact sound hit

theorem Resident.read_capture [DecidableEq Name] (codec : BlockCodec Name Key Payload) (input : Read Name)
    (names : List Name) : (capture codec input names).read = readBlock codec (restrict input names) :=
  Proofs.Formats.Dasl.Arena.Prolly.read_capture codec input names

theorem Resident.lookup_capture [DecidableEq Name] [LinearOrder Key] (codec : BlockCodec Name Key Payload)
    (input : Read Name) (names : List Name) (width fuel : Nat) (root : Name) (key : Key) :
    (capture codec input names).lookup width fuel root key = routedLookup codec (restrict input names) width fuel root key :=
  congrArg (fun reader => Silmaril.Formats.Dasl.Prolly.route reader width key fuel none root) (read_capture codec input names)

/-- Either successful answer, including verified absence, requires a valid rooted reference.
The observation need not contain all reference blocks, and no backward naming uniqueness is used. -/
theorem Resident.lookup_sound [DecidableEq Name] [LinearOrder Key] {codec : BlockCodec Name Key Payload}
    {input : Read Name} {names : List Name} {tree : Semantics.Prolly.Tree Key Payload}
    (routable : tree.Routable)
    {address : Block Name Key Payload → Name} {store : Store Name} (stored : Stored codec address tree store)
    (bound : store.Binding) (sound : Read.Sound input store) {width fuel : Nat} {key : Key} {result : Option Payload}
    (checked : (capture codec input names).lookup width fuel (tree.rootName address) key = .ok result) :
    tree.entries.lookup key = result :=
  routedLookup_sound routable stored bound (restrict_sound sound names)
    ((lookup_capture codec input names width fuel (tree.rootName address) key) ▸ checked)

theorem Resident.lookup_complete [DecidableEq Name] [LinearOrder Key] {codec : BlockCodec Name Key Payload}
    {input : Read Name} {names : List Name} {tree : Semantics.Prolly.Tree Key Payload}
    {address : Block Name Key Payload → Name}
    {width fuel : Nat} {key : Key} (routable : tree.Routable) (bounded : tree.Bounded width)
    (reads : PathReads (capture codec input names).read address key tree.level tree.root) (enough : tree.level < fuel) :
    (capture codec input names).lookup width fuel (tree.rootName address) key = .ok (tree.entries.lookup key) := by
  rw [lookup_capture]
  exact routedLookup_complete routable bounded ((read_capture codec input names) ▸ reads) enough

end Silmaril.Formats.Dasl.Arena.Prolly
