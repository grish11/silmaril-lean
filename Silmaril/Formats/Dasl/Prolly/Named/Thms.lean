module

public import Silmaril.Formats.Dasl.Prolly.Named.Defs
public import Silmaril.Formats.Dasl.Named.Thms
public import Silmaril.Formats.Dasl.Prolly.Root.Thms
import Silmaril.Proofs.Formats.Dasl.ProllyNamed

public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload : Type} {store : Store Name}

/-- Lift the exact encoded root, not a spelling that merely resolves to the
same nameless value. No new observations are asserted about the store. -/
theorem Stored.namedRoot {key : Encode.TotalCodec Key (Shallow Name)} {payload : Encode.TotalCodec Payload (Shallow Name)}
    {address : Block Name Key Payload → Name} {tree : Silmaril.Semantics.Prolly.Tree Key Payload}
    (stored : Stored (blockCodec key payload) address tree store)
    (ready : NodeReady key payload store tree.level tree.root) :
    ∃ named, (blockCodec key payload).encode? (nodeBlock address tree.level tree.root) = some named.embed.shallow ∧
      FullNames store (tree.rootName address) named :=
  Proofs.Formats.Dasl.ProllyNamed.namedRoot key payload address tree ready stored

namespace RootProfile

variable [LinearOrder Key] (profile : RootProfile Name Key Payload)

theorem namedRoots_subset : Naming.Subset (profile.NamedRoots store) profile.Roots :=
  fun _ _ ⟨_, map, address, lookup, admits, nameEq, _⟩ => ⟨map, address, lookup, admits, nameEq⟩

theorem namedRoots_mono {extension : Store Name} (incl : store.Subset extension) (bound : extension.Binding) :
    Naming.Subset (profile.NamedRoots store) (profile.NamedRoots extension) :=
  fun _ _ ⟨_, map, address, lookup, admits, nameEq, stored, tree, spelling, expansion⟩ =>
    ⟨bound, map, address, lookup, admits, nameEq, stored.mono incl, tree, spelling, expansion.mono incl⟩

/-- Naming and structural storage alone do not imply that key or payload
targets are present. `ready` supplies those additional witnesses. -/
theorem namedRoot_of_stored {map : OrderedMap Key Payload} {root : Name}
    (bound : store.Binding) (named : profile.rootName? map = some root)
    (stored : Stored (blockCodec profile.key profile.payload) (replayAddress profile.nameBlock? root)
      (build profile.policy map) store)
    (ready : NodeReady profile.key profile.payload store (build profile.policy map).level (build profile.policy map).root) :
    profile.NamedRoots store root map.lookup? :=
  Proofs.Formats.Dasl.ProllyNamed.namedRoot_of_stored profile bound named stored ready

theorem namedRootNames_singleton {map : OrderedMap Key Payload} {root : Name}
    (found : profile.NamedRoots store root map.lookup?) : Naming.names (profile.NamedRoots store) map.lookup? = {root} :=
  Naming.names_eq_singleton_iff.mpr ⟨found, fun _ candidate => Option.some.inj
    (((profile.roots_iff _ _).mp (profile.namedRoots_subset candidate)).symm.trans
      ((profile.roots_iff _ _).mp (profile.namedRoots_subset found)))⟩

end RootProfile
end Silmaril.Formats.Dasl.Prolly
