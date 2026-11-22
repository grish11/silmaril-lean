module

public import Silmaril.Formats.Git.Filesystem.Defs
public import Silmaril.Formats.Dasl.Prolly.Scan.Thms

public section

namespace Silmaril.Proofs.Formats.Git.Filesystem

open Silmaril.Formats.Git Silmaril.Formats.Git.Filesystem
open Silmaril.Formats.Git.Arena (CasLane Read)
open Silmaril.Formats.Dasl.Prolly (ByteKey)
open Silmaril.Semantics

variable {hash : Hash} {Ref Meta : Type}

theorem names_iff {relation : Naming.Relation Cid ByteArray} {tree : Object ByteKey Ref Meta .tree}
    {image : Image hash .tree} {name : Cid} (staged : stage hash tree = .ok image)
    (covers : ∃ cid, relation cid image.bytes)
    (agrees : ∀ cid wire, relation cid wire → cid = address hash .object wire) :
    Names hash relation name tree ↔ name = image.name := by
  constructor
  · rintro ⟨actual, received, proof⟩
    have same := Except.ok.inj (staged.symm.trans received)
    subst actual
    exact agrees name image.bytes proof
  · rintro rfl
    obtain ⟨cid, proof⟩ := covers
    have same : cid = image.name := agrees cid image.bytes proof
    exact ⟨image, staged, same ▸ proof⟩

theorem published_root {kind : Kind} {image : Image hash kind} {before after : Cid → Option ByteArray}
    (published : image.publish before = .ok after) : after (image.name) = some image.bytes := by
  change Naming.graph after (image.name) image.bytes
  rw [Naming.admit_eq_union published]
  exact Or.inr (List.mem_cons_self ..)

theorem readVerified_found {store : Store} {lane : CasLane} {name : Cid} {bytes : ByteArray}
    (found : readVerified hash store lane name = .found bytes) :
    store lane name = .found bytes ∧ address hash lane bytes = name := by
  by_cases laneOK : laneMatches lane name = true
  · cases src : store lane name <;> simp [readVerified, laneOK, src, Read.andThen] at found
    rename_i value
    split at found
    · rename_i matching
      cases found
      exact ⟨rfl, matching⟩
    · contradiction
  · simp [readVerified, laneOK] at found

theorem checkedChild_ok {store : Store}
    {query : Cid → ByteKey → Except (Formats.Dasl.Prolly.Fault Cid) (Option (Entry Cid))}
    {root : Cid} {key : ByteKey} {result : Option (Entry Cid)}
    (checked : checkedChild store query root key = .ok result) : query root key = .ok result := by
  by_cases keyOK : Dasl.validByteComponent key = true
  · cases looked : query root key with
    | error fault => simp [checkedChild, keyOK, looked, Except.mapError, Bind.bind, Except.bind] at checked
    | ok value =>
      cases value with
      | none => simpa [checkedChild, keyOK, looked, Except.mapError, Bind.bind, Except.bind] using checked
      | some entry =>
        simp [checkedChild, keyOK, looked, Except.mapError, Bind.bind, Except.bind] at checked
        split at checked
        · contradiction
        · simp_all
  · simp [checkedChild, keyOK, throw, throwThe, Bind.bind, Except.bind] at checked

end Silmaril.Proofs.Formats.Git.Filesystem
