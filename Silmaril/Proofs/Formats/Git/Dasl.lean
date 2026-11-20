module

public import Silmaril.Formats.Git.Dasl.Defs
public import Silmaril.Formats.Git.Thms

public section

namespace Silmaril.Proofs.Formats.Git

open Silmaril.Formats.Git Silmaril.Formats.Git.Dasl
open Silmaril.Formats.Dasl (Shallow)

theorem entry_roundtrip {Name : Type} (entry : Entry Name) : decodeEntry (encodeEntry entry) = some entry := by
  obtain ⟨mode, name⟩ := entry
  cases mode with
  | file mode => cases mode <;> rfl
  | directory | gitlink => rfl

theorem utf8_roundtrip (name : String) : decodeUtf8Key (utf8Key name) = some name := by
  have bytes : ((utf8Key name).map UInt8.ofFin).toByteArray = name.toByteArray := by
    simp [ByteArray.ext_iff, utf8Key, bytesKey, List.map_map, Function.comp_def]
  rw [decodeUtf8Key, bytes, String.fromUTF8?, dite_eq_left name.isValidUTF8]
  rfl

theorem ordered_lookup {Key Item : Type} [LinearOrder Key] (dir : Directory Key Item) (key : Key) :
    dir.ordered.lookup? key = dir.lookup key := by
  by_cases member : key ∈ dir.keys
  · simpa [Directory.lookup, member] using
      dir.ordered.lookup_eq_some_iff.mpr (List.mem_pmap_of_mem ((Finset.mem_sort _).mpr member))
  · cases hit : dir.ordered.lookup? key with
    | none => simp [Directory.lookup, member]
    | some value =>
      have found := dir.ordered.lookup_eq_some_iff.mp hit
      obtain ⟨other, present, same⟩ := List.mem_pmap.mp found
      have equal := congrArg Prod.fst same
      change other = key at equal
      exact (member (equal ▸ (Finset.mem_sort _).mp present)).elim

theorem ofOrdered_lookup {Key Item : Type} [LinearOrder Key] (dir : Semantics.OrderedMap Key Item) (key : Key) :
    (Directory.ofOrdered dir).lookup key = dir.lookup? key := by
  cases hit : dir.lookup? key with
  | none =>
    have missing : key ∉ dir.keys.toFinset := by
      intro found
      obtain ⟨⟨other, value⟩, present, same⟩ := List.mem_map.mp (List.mem_toFinset.mp found)
      change other = key at same
      subst other
      rw [dir.lookup_eq_some_iff.mpr present] at hit
      contradiction
    simp [Directory.lookup, Directory.ofOrdered, missing]
  | some value =>
    have member : key ∈ dir.keys.toFinset := List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨(key, value), dir.lookup_eq_some_iff.mp hit, rfl⟩)
    have found : (Directory.ofOrdered dir).lookup key = some ((Directory.ofOrdered dir).get ⟨key, member⟩) := by
      unfold Directory.lookup
      exact dite_eq_left member
    exact found.trans ((Option.some_get _).trans hit)

theorem render_embedding {Name Meta : Type} (naming : Naming Name) (layout : Layout String Name)
    (codec : Silmaril.Formats.Dasl.Encode.TotalCodec Meta (Shallow Name)) (tree : Tree) :
    renderObject naming layout validComponent codec tree.toObject = renderTree naming layout tree := by
  induction tree with
  | file => rfl
  | dir names children ih =>
    simp only [Tree.toObject, renderObject, renderTree]
    rw [funext ih]

end Silmaril.Proofs.Formats.Git
