module

public import Silmaril.Formats.Git.Filesystem.Defs
public import Silmaril.Formats.Dasl.Arena.Prolly.Defs

@[expose] public section

namespace Silmaril.Formats.Git.Filesystem

open Formats.Dasl.Arena.Prolly (Reader Resident)
open Formats.Dasl.Prolly (ByteKey readBlock route)

def dirReader (hash : Hash) (store : Store) : Reader Cid ByteKey (Entry Cid) := readBlock dirCodec (dirRead hash store)

/-- On-demand traversal visits only the selected Prolly branch. It uses the
same verification, component checks and edge policy as the closed scan. -/
def lookupChildRouted (hash : Hash) (store : Store) (fuel : Nat) : ChildLookup :=
  checkedChild store fun root key => route (dirReader hash store) policy.width key fuel none root

/-- Route over explicitly acquired observations from this store. An unacquired
block is a read fault, not an absent entry. -/
def lookupChildResident (hash : Hash) (store : Store) (acquired : List Cid) (fuel : Nat) : ChildLookup :=
  let resident := Resident.capture dirCodec (dirRead hash store) acquired
  checkedChild store fun root key => resident.lookup policy.width fuel root key

def locateRouted (hash : Hash) (store : Store) (fuel : Nat) := locateWith (lookupChildRouted hash store fuel)

def locateResident (hash : Hash) (store : Store) (acquired : List Cid) (fuel : Nat) :=
  locateWith (lookupChildResident hash store acquired fuel)

end Silmaril.Formats.Git.Filesystem
