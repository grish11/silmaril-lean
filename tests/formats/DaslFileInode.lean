module

import Batteries.Data.Except
import Silmaril.Formats.Dasl.FileInode.Thms
meta import Silmaril.Formats.Dasl.FileInode.Defs

open Silmaril.Formats.Dasl Silmaril.Formats.Cbor

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def limits : FileInode.Limits := ⟨2, 3, by decide, by decide⟩

private def cid (profile : Drisl.CidProfile) (hash kind seed : UInt8) : IO (Drisl.Cid profile) := do
  let some name := (Drisl.Cid.codec profile).parse? ([1, kind, hash, 0x20] ++ List.replicate 32 seed)
    | throw (IO.userError "fixture CID")
  return name

private def checkFile {profile : Drisl.CidProfile} (wire : Wire.Profile (Drisl.Cid profile))
    (adapt : (Drisl.Cid profile → Option ByteArray) → FileInode.Snapshot (Drisl.Cid profile)) (hash : UInt8) : IO Unit := do
  let root ← cid profile hash 0x71 1
  let nested ← cid profile hash 0x71 2
  let first ← cid profile hash 0x55 3
  let last ← cid profile hash 0x55 4
  let codec := wire.codec FileInode.codec
  let entries : FileInode.Inode _ := [⟨.blob first, 3⟩, ⟨.obj nested, 2⟩]
  let some rootBytes := codec.encode? entries | throw (IO.userError "root encoding")
  let some nestedBytes := codec.encode? [⟨.blob last, 2⟩] | throw (IO.userError "child encoding")
  check (decide (codec.decode? rootBytes = some entries)) "wire layout round trip"
  check ((codec.encode? [⟨.blob root, 1⟩]).isNone && (codec.encode? [⟨.obj first, 1⟩]).isNone)
    "wire rejects mismatched CID tags"
  let full := fun name =>
    if name = root then some rootBytes else if name = nested then some nestedBytes
    else if name = first then some ⟨#[10, 11, 12]⟩ else if name = last then some ⟨#[13, 14]⟩ else none
  let partialView := adapt fun name => if name = nested then none else full name
  let invalidOffPath := adapt fun name => if name = nested then some ⟨#[0xff]⟩ else full name
  let request := FileInode.read limits (adapt full)
  check (decide (request 3 root none = .ok [10, 11, 12, 13, 14])) "whole file recovery"
  check (decide (request 3 root (some (2, 2)) = .ok [12, 13])) "cross-page range"
  check (decide (request 3 root (some (3, 2)) = .ok [13, 14])) "aligned child boundary"
  check (decide (FileInode.read limits partialView 2 root (some (0, 3)) = .ok [10, 11, 12])) "skip missing subtree"
  check (decide (FileInode.read limits invalidOffPath 2 root (some (1, 2)) = .ok [11, 12])) "skip invalid subtree"
  check (decide (FileInode.read limits partialView 1 root (some (5, 0)) = .ok [])) "empty read at EOF"
  check (decide (FileInode.read limits partialView 2 root (some (3, 1)) = .error (.missing (.obj nested)))) "missing is explicit"
  check (decide (FileInode.read limits invalidOffPath 2 root (some (3, 1)) = .error (.invalid (.obj nested)))) "malformed inode is explicit"
  check (decide (request 3 root (some (4, 2)) = .error (.outOfBounds 5))) "no clipping past EOF"
  check (decide (request 2 root (some (2, 2)) = .error (.fuel (.blob last)))) "depth fuel is explicit"
  check (decide (request 2 first none = .error (.invalid (.obj first)))) "reject raw CID as inode"
  let wrongPage := adapt fun name => if name = first then some ⟨#[10, 11]⟩ else full name
  check (decide (FileInode.read limits wrongPage 3 root (some (0, 1)) = .error (.invalid (.blob first)))) "reject truncated page even on prefix read"
  let tinyLimits : FileInode.Limits := ⟨2, 2, by decide, by decide⟩
  check (decide (FileInode.read tinyLimits (adapt full) 3 root (some (0, 1)) = .error (.invalid (.blob first)))) "enforce page limit"
  let narrowLimits : FileInode.Limits := ⟨1, 3, by decide, by decide⟩
  check (decide (FileInode.read narrowLimits (adapt full) 3 root (some (0, 1)) = .error (.invalid (.obj root)))) "enforce fanout limit"
  let invalidLength := adapt fun name =>
    if name = nested then codec.encode? [⟨.blob last, 1⟩] else full name
  check (decide (FileInode.read limits invalidLength 3 root (some (3, 1)) = .error (.invalid (.obj nested)))) "enforce exact child inode length"
  let zeroLength := adapt fun _ => codec.encode? [⟨.blob last, 0⟩]
  check (decide (FileInode.read limits zeroLength 3 root none = .error (.invalid (.obj root)))) "reject a zero child length"
  let empty := adapt fun _ => codec.encode? []
  check (decide (FileInode.read limits empty 1 root none = .ok [])) "empty inode is the empty file"

public def main : IO Unit := do
  checkFile Wire.Profile.dasl FileInode.daslSnapshot 0x12
  checkFile Wire.Profile.bdasl FileInode.bdaslSnapshot 0x1e
