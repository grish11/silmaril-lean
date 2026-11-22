module

import Batteries.Data.Except
import Silmaril.Formats.Git.Filesystem.Writer.Readback
import Silmaril.Formats.Dasl.Wire.Canonical.Thms
meta import Silmaril.Formats.Git.Filesystem.Defs
meta import Silmaril.Formats.Dasl.Prolly.Route.Defs

open Silmaril.Formats.Git
open Silmaril.Formats.Git.Filesystem
open Silmaril.Formats.Dasl.Prolly (ByteKey routedLookup)

private def emptyTree : Object ByteKey Empty Unit .tree :=
  .tree ∅ (fun child => (Finset.notMem_empty _ child.property).elim)
    (fun child => (Finset.notMem_empty _ child.property).elim)

private def testHash : Hash := fun _ => ⟨List.replicate 32 0, by simp⟩

private def checksEmpty : Bool := Id.run do
  let .ok image := stage testHash emptyTree | return false
  let .ok fetched := image.publish (fun _ => none) | return false
  let read := dirRead testHash (.ofPublished fetched)
  return image.writes.length == 1 &&
    decide (routedLookup dirCodec read policy.width 1 image.name [255] = .ok none) &&
    decide (lookupChild testHash (.ofPublished fetched) 1 image.name [255] = .ok none)

#guard checksEmpty

example (hash : Hash) (bytes : ByteArray) : ∃ image,
    stage hash (.blob (Ref := Empty) (Meta := Unit) bytes) = .ok image := stage_of_bounds trivial

#print axioms Silmaril.Formats.Dasl.Wire.bdasl_roundtrip
#print axioms BlockBounds.encode
#print axioms stageDirectory_of_root
#print axioms stageDirectory_of_bounds
#print axioms stageDirectory_of_ok
#print axioms stage_of_bounds
#print axioms Image.directory_readback
#print axioms readback_of_stage
#print axioms Image.readbackPublished
