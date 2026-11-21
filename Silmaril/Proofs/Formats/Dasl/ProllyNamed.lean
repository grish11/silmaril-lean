module

public import Silmaril.Formats.Dasl.Named.Thms
public import Silmaril.Formats.Dasl.Prolly.Named.Defs
public import Silmaril.Formats.Dasl.Prolly.Root.Thms
import all Silmaril.Formats.Dasl.Encode.Thms
import all Silmaril.Formats.Dasl.Encode.Map.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyNamed

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload : Type} {store : Store Name}

private theorem liftList {items : List (Shallow Name)}
    (ready : ∀ source ∈ items, ExpansionReady store source) : ExpansionReady store (Encode.list.encode items) := by
  let lift (index : Fin items.length) := ready (items.get index) (List.get_mem items index)
  exact ⟨.list items.length (fun index => Classical.choose (lift index)),
    .list (fun index => Classical.choose_spec (lift index))⟩

private theorem liftPair {left right : Shallow Name}
    (first : ExpansionReady store left) (second : ExpansionReady store right) :
    ExpansionReady store (Encode.pairEntry.encode (left, right)) := by
  obtain ⟨firstValue, first⟩ := first
  obtain ⟨secondValue, second⟩ := second
  refine ⟨.list 2 (fun index => if index.val = 0 then firstValue else secondValue), .list ?_⟩
  intro index
  change CanName store (if index.val = 0 then firstValue else secondValue) (if index.val = 0 then left else right)
  split <;> assumption

private theorem liftEntries {Item : Type} (key : Encode.TotalCodec Key (Shallow Name))
    (item : Encode.TotalCodec Item (Shallow Name)) (entries : List (Key × Item))
    (ready : ∀ row ∈ entries, ExpansionReady store (key.encode row.1) ∧ ExpansionReady store (item.encode row.2)) :
    ExpansionReady store ((entriesCodec key item).encode entries) := by
  apply liftList
  intro source present
  obtain ⟨row, hit, rfl⟩ := List.mem_map.mp present
  exact liftPair (ready row hit).1 (ready row hit).2

theorem expandNode (key : Encode.TotalCodec Key (Shallow Name)) (payload : Encode.TotalCodec Payload (Shallow Name))
    (address : Block Name Key Payload → Name) (level : Nat) (node : Node Key Payload level)
    (ready : NodeReady key payload store level node) (stored : Stored (blockCodec key payload) address ⟨level, node⟩ store) :
    ∃ source, (blockCodec key payload).encode? (nodeBlock address level node) = some source ∧
      store.objects (address (nodeBlock address level node)) source ∧ ExpansionReady store source := by
  obtain ⟨source, encoded, present⟩ := stored (nodeBlock address level node) (by cases level <;> simp [blockOccurrences])
  refine ⟨source, encoded, present, ?_⟩
  rw [blockCodec_encode] at encoded
  cases level with
  | zero =>
    change some (Encode.list.encode [.string "leaf", (entriesCodec key payload).encode node]) = some source at encoded
    cases encoded
    apply liftList
    intro child hit
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl
    · exact ⟨_, .string _⟩
    · exact liftEntries key payload node ready
  | succ height =>
    let children := node.map fun row => (row.1, address (nodeBlock address height row.2))
    change (if 0 < height + 1 ∧ height + 1 < 2^63 then some (Encode.list.encode
      [.string "branch", .i64 (UInt64.ofNat (height + 1)), (entriesCodec key objectLink).encode children]) else none) =
        some source at encoded
    split at encoded
    · cases encoded
      apply liftList
      intro child hit
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
      rcases hit with rfl | rfl | rfl
      · exact ⟨_, .string _⟩
      · exact ⟨_, .i64 _⟩
      · apply liftEntries key objectLink children
        intro row hit
        obtain ⟨child, inNode, rfl⟩ := List.mem_map.mp hit
        refine ⟨(ready child inNode).1, ?_⟩
        have childStored : Stored (blockCodec key payload) address ⟨height, child.2⟩ store := by
          intro block hit
          exact stored block (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, inNode, hit⟩))
        obtain ⟨_, _, present, value, choices⟩ := expandNode key payload address height child.2 (ready child inNode).2 childStored
        exact ⟨Value.obj value, .obj choices present⟩
    · cases encoded
termination_by level

theorem namedRoot (key : Encode.TotalCodec Key (Shallow Name)) (payload : Encode.TotalCodec Payload (Shallow Name))
    (address : Block Name Key Payload → Name) (tree : Silmaril.Semantics.Prolly.Tree Key Payload)
    (ready : NodeReady key payload store tree.level tree.root)
    (stored : Stored (blockCodec key payload) address tree store) :
    ∃ named, (blockCodec key payload).encode? (nodeBlock address tree.level tree.root) = some named.embed.shallow ∧
      FullNames store (tree.rootName address) named := by
  obtain ⟨source, encoded, present, value, choices⟩ := expandNode key payload address tree.level tree.root ready stored
  obtain ⟨named, _, same, admitted⟩ := canName_iff_exists_admitted.mp choices
  exact ⟨named, same ▸ encoded, source, present, same ▸ Named.admitted_iff_expands.mp admitted⟩

theorem namedRoot_of_stored [LinearOrder Key] (profile : RootProfile Name Key Payload)
    {map : OrderedMap Key Payload} {root : Name} (bound : store.Binding) (named : profile.rootName? map = some root)
    (stored : Stored (blockCodec profile.key profile.payload) (replayAddress profile.nameBlock? root)
      (build profile.policy map) store)
    (ready : NodeReady profile.key profile.payload store (build profile.policy map).level (build profile.policy map).root) :
    profile.NamedRoots store root map.lookup? := by
  let tree := build profile.policy map
  let address := replayAddress profile.nameBlock? root
  obtain ⟨admits, rootEq⟩ := tree.replayAddress_spec profile.nameBlock? root named
  obtain ⟨expanded, exactEncoding, resolves⟩ := namedRoot profile.key profile.payload address tree ready stored
  exact ⟨bound, map, address, fun _ => rfl, admits, rootEq, stored, expanded,
    by simpa only [blockCodec_encode] using exactEncoding, rootEq ▸ resolves⟩

end Silmaril.Proofs.Formats.Dasl.ProllyNamed
