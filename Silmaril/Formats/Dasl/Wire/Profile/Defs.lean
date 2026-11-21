module

public import Silmaril.Formats.Dasl.Encode.Defs
public import Silmaril.Formats.Dasl.Wire.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Wire

open Silmaril.Formats.Cbor

/-- Object wire syntax and eligibility as an object root, without a digest algorithm
or a claim that all trees over `Name` can be serialized. -/
structure Profile (Name : Type) where
  render? : Shallow Name → Option ByteArray
  parse? : ByteArray → Option (Shallow Name)
  objectName : Name → Bool

def linkSupported {profile : Drisl.CidProfile} : Link (Drisl.Cid profile) → Bool
  | .obj cid => cid.val[1]? == some 0x71
  | .blob cid => cid.val[1]? == some 0x55

def Profile.dasl : Profile Cid := ⟨Wire.render?, Wire.parse?, fun cid => linkSupported (.obj cid)⟩

abbrev BdaslCid := Drisl.Cid .bdasl

def bdaslCidCodec : Drisl.CidCodec (Link BdaslCid) where
  bytes
    | .obj cid | .blob cid => cid.val
  parse? bytes := do
    let cid ← (Drisl.Cid.codec .bdasl).parse? bytes
    if linkSupported (.obj cid) then some (.obj cid)
    else if linkSupported (.blob cid) then some (.blob cid)
    else none

/-- Signed-i64 DRISL objects with the DASL or BDASL CID envelope. This does not
compute digests or check streaming proofs. -/
def Profile.bdasl : Profile BdaslCid where
  render? value := do
    let ordered := toOrdered value
    if (Drisl.links ordered).all linkSupported then
      (Drisl.renderCbor? Drisl.i64Cbor bdaslCidCodec ordered).map List.toByteArray
    else none
  parse? bytes := (Drisl.parseCbor? Drisl.i64Cbor bdaslCidCodec bytes.data.toList).map lower
  objectName cid := linkSupported (.obj cid)

variable {Name Source : Type}

def Profile.decode? (profile : Profile Name) (layout : Encode.TotalCodec Source (Shallow Name))
    (bytes : ByteArray) : Option Source := (profile.parse? bytes).bind layout.decode?

/-- Recover a layout from the caller's store. This does not verify the digest. -/
def Profile.read? (profile : Profile Name) (layout : Encode.TotalCodec Source (Shallow Name))
    (read : Name → Option ByteArray) (name : Name) : Option Source :=
  if profile.objectName name then (read name).bind (profile.decode? layout) else none

/-- Emit only when the selected reader recovers this layout. The check is on the
source type; a decision procedure for equality of arbitrary DASL trees is not needed. -/
def Profile.codec (profile : Profile Name) (layout : Encode.TotalCodec Source (Shallow Name))
    [DecidableEq Source] : Encode.PartialCodec Source ByteArray where
  decode? := profile.decode? layout
  encode? source := (profile.render? (layout.encode source)).bind fun bytes =>
    if profile.decode? layout bytes = some source then some bytes else none
  recovers _ _ hit := by
    obtain ⟨_, _, checked⟩ := Option.bind_eq_some_iff.mp hit
    split at checked <;> simp_all

/-- Only the canonical encoder's image is named here, even if the parser is more permissive. -/
def Profile.roots (profile : Profile Name) (layout : Encode.TotalCodec Source (Shallow Name))
    [DecidableEq Source] (store : Semantics.Naming.Relation Name ByteArray) :
    Semantics.Naming.Relation Name Source :=
  fun name source => profile.objectName name = true ∧ Encode.codedNames store (profile.codec layout) name source

end Silmaril.Formats.Dasl.Wire
