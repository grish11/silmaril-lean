module

public import Silmaril.Formats.Dasl.Prolly.Replace.Defs
public import Silmaril.Formats.Dasl.Prolly.Route.Thms
public import Silmaril.Formats.Dasl.Prolly.Root.Publish.Thms
import Silmaril.Proofs.Formats.Dasl.ProllyReplaceLayout

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyReplace

open Silmaril.Semantics Silmaril.Semantics.Prolly Silmaril.Semantics.Naming
open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Formats.Dasl.Prolly.RootProfile

variable {Name Key Payload : Type}

private theorem patch_split {Item : Type} (test : Item → Bool) (earlier suffix : List Item) (old next : Item)
    (before : ∀ item ∈ earlier, !test item) (atHit : test old) :
    patchFirst test next (earlier ++ old :: suffix) = earlier ++ next :: suffix := by
  induction earlier with
  | nil => simp [patchFirst, atHit]
  | cons head rest ih =>
    have skip := before head List.mem_cons_self
    have tail := ih (fun item hit => before item (List.mem_cons_of_mem _ hit))
    simpa [patchFirst, skip] using congrArg (head :: ·) tail

private theorem emit_spec {profile : RootProfile Name Key Payload} {old : Name} {block : Block Name Key Payload}
    {previous : Payload} {writes : List (Name × ByteArray)} {planned : Replacement Name Payload}
    (hit : profile.emitReplacement old block previous writes = .ok planned) :
    ∃ value bytes, encodeBlock profile.key profile.payload block = some value ∧
      profile.render? value = some bytes ∧ profile.hash? bytes = some planned.root ∧
      planned.previous = previous ∧ planned.writes = (planned.root, bytes) :: writes := by
  unfold emitReplacement at hit
  split at hit <;> try contradiction
  rename_i value encoded
  split at hit <;> try contradiction
  rename_i bytes rendered
  split at hit <;> try contradiction
  rename_i name named
  cases hit
  exact ⟨value, bytes, encoded, rendered, named, rfl, rfl⟩

private theorem emit_ne_absent (profile : RootProfile Name Key Payload) (old : Name) (block : Block Name Key Payload)
    (previous : Payload) (writes : List (Name × ByteArray)) :
    profile.emitReplacement old block previous writes ≠ .error .absent := by
  simp only [emitReplacement]
  split
  · split
    · split <;> (intro bad; cases bad)
    · intro bad; cases bad
  · intro bad; cases bad

theorem plan_absent [LinearOrder Key] (profile : RootProfile Name Key Payload)
    (read : Name → Except (Fault Name) (Block Name Key Payload)) (key : Key) (value : Payload)
    (fuel : Nat) (expected : Option Nat) (root : Name)
    (absent : profile.planReplacement read key value fuel expected root = .error .absent) :
    route read profile.policy.width key fuel expected root = .ok none := by
  induction fuel generalizing expected root with
  | zero => simp [planReplacement] at absent
  | succ fuel ih =>
    cases readEq : read root with
    | error fault => simp [planReplacement, readEq, Except.mapError, Except.bind, bind] at absent
    | ok block =>
      cases block with
      | leaf entries =>
        simp only [planReplacement, route, readEq, Except.mapError, bind, Except.bind] at absent ⊢
        split at absent
        · rename_i valid
          rw [ite_eq_left valid]
          split at absent
          · rename_i found
            rw [found]
          · exact (emit_ne_absent _ _ _ _ _ absent).elim
        · cases absent
      | branch level children =>
        simp only [planReplacement, route, readEq, Except.mapError, bind, Except.bind] at absent ⊢
        split at absent
        · rename_i valid
          rw [ite_eq_left valid]
          split at absent
          · rename_i found
            simp [found]
          · rename_i child found
            rw [found]
            cases rec : profile.planReplacement read key value fuel (some (level - 1)) child.2 with
            | error failure =>
              simp [rec] at absent
              subst failure
              exact ih _ _ rec
            | ok result =>
              simp only [rec] at absent
              exact (emit_ne_absent _ _ _ _ _ absent).elim
        · cases absent

private theorem root_mem (address : Block Name Key Payload → Name) (level : Nat) (node : Node Key Payload level) :
    nodeBlock address level node ∈ blockOccurrences address level node := by
  cases level <;> simp [blockOccurrences]

private theorem child_mem {address : Block Name Key Payload → Name} {level : Nat}
    {children : Node Key Payload (level + 1)} {child : Key × Node Key Payload level}
    (hit : child ∈ children) {block : Block Name Key Payload} (below : block ∈ blockOccurrences address level child.2) :
    block ∈ blockOccurrences address (level + 1) children :=
  List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, hit, below⟩)

private theorem exact_read {profile : RootProfile Name Key Payload} (reader : profile.Readback)
    {observed : Name → Option ByteArray} {reference : Relation Name ByteArray}
    (includes : Subset (graph observed) reference) (bound : Binding reference)
    {name : Name} {block seen : Block Name Key Payload} {value : Shallow Name} {bytes : ByteArray}
    (encoded : encodeBlock profile.key profile.payload block = some value)
    (rendered : profile.render? value = some bytes) (present : reference name bytes)
    (hit : readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed) name = .ok seen) :
    seen = block := by
  cases observedEq : observed name with
  | none => simp [Readback.pathReader, readBlock, observedEq] at hit
  | some old =>
    have same := bound (includes observedEq) present
    have parsed := reader.recovers rendered
    have decoded := (blockCodec profile.key profile.payload).recovers (by simpa [blockCodec_encode] using encoded)
    simpa [readBlock, Readback.pathReader, observedEq, same, parsed, decoded] using hit.symm

private theorem plan_edit [LinearOrder Key] (profile : RootProfile Name Key Payload) (reader : profile.Readback)
    {observed : Name → Option ByteArray} {reference : Relation Name ByteArray}
    (includes : Subset (graph observed) reference) (bound : Binding reference) (fallback : Name)
    (key : Key) (value : Payload) (level : Nat) (node : Node Key Payload level)
    (stored : profile.NodeBytes (replayAddress profile.nameBlock? fallback) reference level node)
    (fuel : Nat) (expected : Option Nat) (planned : Replacement Name Payload)
    (checked : profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
      key value fuel expected ((replayAddress profile.nameBlock? fallback)
        (nodeBlock (replayAddress profile.nameBlock? fallback) level node)) = .ok planned) :
    let address := replayAddress profile.nameBlock? fallback
    ∃ next, Edit key value level node next planned.previous ∧ planned.root = address (nodeBlock address level next) ∧
      planned.writes.length = level + 1 ∧ profile.NodeBytes address (union reference (listed planned.writes)) level next := by
  let address := replayAddress profile.nameBlock? fallback
  let read := readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed)
  change ∃ next, Edit key value level node next planned.previous ∧ planned.root = address (nodeBlock address level next) ∧
    planned.writes.length = level + 1 ∧ profile.NodeBytes address (union reference (listed planned.writes)) level next
  induction level generalizing fuel expected planned with
  | zero =>
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      let old := address (nodeBlock address 0 node)
      change profile.planReplacement read key value (fuel+1) expected old = .ok planned at checked
      obtain ⟨oldValue, oldBytes, encoded, rendered, _, present⟩ := stored _ (root_mem address 0 node)
      cases seen : read old with
      | error reason => simp [planReplacement, seen, Except.mapError, bind, Except.bind] at checked
      | ok decoded =>
        have eq := exact_read reader includes bound encoded rendered present seen
        subst decoded
        simp only [planReplacement, seen, nodeBlock, Except.mapError, bind, Except.bind] at checked
        split at checked <;> try contradiction
        split at checked <;> try contradiction
        rename_i previous found
        obtain ⟨earlier, suffix, split, before⟩ := List.lookup_eq_some_iff.mp found
        have patched : patchFirst (fun entry : Key × Payload => decide (key = entry.1)) (key, value) node =
            earlier ++ (key, value) :: suffix := by
          rw [split]
          exact patch_split _ _ _ _ _ (by simpa using before) (by simp)
        rw [patched] at checked
        obtain ⟨newValue, bytes, newEncoded, newRendered, named, prev, writes⟩ := emit_spec checked
        have nameEq : address (.leaf (earlier ++ (key, value) :: suffix)) = planned.root := by
          simp [address, replayAddress, RootProfile.nameBlock?, newEncoded, newRendered, named]
        refine ⟨_, ?_, nameEq.symm, by simp [writes], ?_⟩
        · rw [split, prev]
          exact .leaf _ _ _
        · intro block hit
          simp only [blockOccurrences, nodeBlock, List.mem_singleton] at hit
          subst block
          refine ⟨newValue, bytes, newEncoded, newRendered, by rwa [nameEq], Or.inr ?_⟩
          simp [writes, nameEq, listed]
  | succ level ih =>
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      let old := address (nodeBlock address (level + 1) node)
      let label : Key × Node Key Payload level → Key × Name := fun child => (child.1, address (nodeBlock address level child.2))
      change profile.planReplacement read key value (fuel+1) expected old = .ok planned at checked
      obtain ⟨oldValue, oldBytes, encoded, rendered, _, present⟩ := stored _ (root_mem address (level + 1) node)
      cases seen : read old with
      | error reason => simp [planReplacement, seen, Except.mapError, bind, Except.bind] at checked
      | ok decoded =>
        have eq := exact_read reader includes bound encoded rendered present seen
        subst decoded
        simp only [planReplacement, seen, nodeBlock, Except.mapError, bind, Except.bind] at checked
        change (if _ then (match selectChild key (node.map label) with | none => _ | some _ => _) else _) = _ at checked
        split at checked <;> try contradiction
        have selection : selectChild key (node.map label) = (selectChild key node).map label := by
          simp [selectChild, label, Function.comp_def]
        rw [selection] at checked
        cases found : selectChild key node with
        | none => simp [found] at checked
        | some child =>
          simp only [found, Option.map_some] at checked
          cases part : profile.planReplacement read key value fuel (some level) (label child).2 with
          | error reason => simp [part] at checked
          | ok below =>
            simp only [Nat.add_sub_cancel, part] at checked
            have childIn := List.mem_of_find?_eq_some found
            have childStored : profile.NodeBytes address reference level child.2 :=
              fun block hit => stored block (child_mem childIn hit)
            obtain ⟨next, edit, nextRoot, nextLength, nextStored⟩ := ih child.2 childStored fuel _ below part
            obtain ⟨atHit, earlier, suffix, split, before⟩ := List.find?_eq_some_iff_append.mp found
            let patched := earlier ++ (child.1, next) :: suffix
            have patched_labels : patchFirst (fun entry : Key × Name => decide (key ≤ entry.1))
                (child.1, below.root) (node.map label) = patched.map label := by
              rw [split, List.map_append, List.map_cons, patch_split]
              · simp [patched, label, nextRoot]
              · intro item hit
                obtain ⟨source, sourceHit, rfl⟩ := List.mem_map.mp hit
                exact before source sourceHit
              · exact atHit
            rw [patched_labels] at checked
            obtain ⟨newValue, bytes, newEncoded, newRendered, named, prev, writes⟩ := emit_spec checked
            have nameEq : address (nodeBlock address (level + 1) patched) = planned.root := by
              simp [address, replayAddress, RootProfile.nameBlock?, nodeBlock, label] at newEncoded ⊢
              simp [newEncoded, newRendered, named]
            refine ⟨patched, ?_, nameEq.symm, by simp [writes, nextLength], ?_⟩
            · rw [split, prev]
              exact .branch _ _ _ edit
            · intro block hit
              simp only [blockOccurrences, List.mem_cons, List.mem_flatMap] at hit
              rcases hit with rfl | ⟨item, itemIn, blockIn⟩
              · refine ⟨newValue, bytes, newEncoded, newRendered, by rwa [nameEq], Or.inr ?_⟩
                simp [writes, nameEq, listed]
              · have liftWrite : Subset (listed below.writes) (listed planned.writes) := by
                  intro _ _ h
                  simp only [listed, writes, List.mem_cons]
                  exact Or.inr h
                rw [show patched = earlier ++ (child.1, next) :: suffix from rfl, List.mem_append, List.mem_cons] at itemIn
                rcases itemIn with pre | rfl | post
                · obtain ⟨v, b, enc, rend, hash, mem⟩ := stored block
                    (child_mem (by rw [split]; exact List.mem_append_left _ pre) blockIn)
                  exact ⟨v, b, enc, rend, hash, Or.inl mem⟩
                · obtain ⟨v, b, enc, rend, hash, mem⟩ := nextStored block blockIn
                  exact ⟨v, b, enc, rend, hash, mem.elim Or.inl (fun h => Or.inr (liftWrite h))⟩
                · obtain ⟨v, b, enc, rend, hash, mem⟩ := stored block (child_mem
                    (by rw [split]; exact List.mem_append_right _ (List.mem_cons_of_mem _ post)) blockIn)
                  exact ⟨v, b, enc, rend, hash, Or.inl mem⟩

theorem replacedMap_lookup [LinearOrder Key] (map : OrderedMap Key Payload) (key query : Key) (value : Payload) :
    (replacedMap map key value).lookup? query =
      (map.lookup? query).map (fun old => if key = query then value else old) := by
  unfold OrderedMap.lookup? replacedMap
  change (map.entries.map (fun entry => (entry.1, if key = entry.1 then value else entry.2))).lookup query = _
  generalize map.entries = entries
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨entryKey, entryValue⟩ := head
    by_cases hit : (query == entryKey) = true
    · have equal := beq_iff_eq.mp hit
      subst entryKey
      simp
    · have skip : (query == entryKey) = false := Bool.eq_false_iff.mpr hit
      simp only [List.map_cons, List.lookup_cons, skip, ih]

theorem storedNode [LinearOrder Key] (profile : RootProfile Name Key Payload) (map : OrderedMap Key Payload)
    {reference : Relation Name ByteArray} {root : Name} (named : profile.rootName? map = some root)
    (present : Subset (profile.byteObservations (build profile.policy map)
      (replayAddress profile.nameBlock? root)) reference) :
    profile.NodeBytes (replayAddress profile.nameBlock? root) reference
      (build profile.policy map).level (build profile.policy map).root := by
  let address := replayAddress profile.nameBlock? root
  have admits := ((build profile.policy map).replayAddress_spec _ root named).1
  intro block hit
  have blockNamed := admits block hit
  cases enc : encodeBlock profile.key profile.payload block with
  | none => simp [RootProfile.nameBlock?, enc] at blockNamed
  | some value =>
    cases ser : profile.render? value with
    | none => simp [RootProfile.nameBlock?, enc, ser] at blockNamed
    | some bytes =>
      refine ⟨value, bytes, rfl, ser, ?_, present ?_⟩
      · simpa [RootProfile.nameBlock?, enc, ser] using blockNamed
      · exact ⟨value, ⟨block, ⟨rfl, hit⟩, enc⟩, ser⟩

theorem rebuild [LinearOrder Key] (profile : RootProfile Name Key Payload) (reader : profile.Readback)
    (map : OrderedMap Key Payload) {root : Name} (named : profile.rootName? map = some root)
    {observed : Name → Option ByteArray} {reference : Relation Name ByteArray}
    (includes : Subset (graph observed) reference) (bound : Binding reference)
    (present : Subset (profile.byteObservations (build profile.policy map)
      (replayAddress profile.nameBlock? root)) reference)
    {fuel : Nat} {key : Key} {value : Payload} {planned : Replacement Name Payload}
    (checked : profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
      key value fuel none root = .ok planned) :
    let oldTree := build profile.policy map
    let newTree := build profile.policy (replacedMap map key value)
    map.lookup? key = some planned.previous ∧ profile.rootName? (replacedMap map key value) = some planned.root ∧
      planned.writes.length = oldTree.level + 1 ∧ profile.NodeBytes (replayAddress profile.nameBlock? root)
        (union reference (listed planned.writes)) newTree.level newTree.root := by
  let tree := build profile.policy map
  let address := replayAddress profile.nameBlock? root
  have oldRoot := (tree.replayAddress_spec _ root named).2
  rw [← oldRoot] at checked
  obtain ⟨next, edit, nextRoot, len, nextStored⟩ := plan_edit profile reader includes bound root key value
    tree.level tree.root (storedNode profile map named present) fuel none planned checked
  have ordered := (build_routable profile.policy map).1
  have newTree : build profile.policy (replacedMap map key value) = ⟨tree.level, next⟩ := by
    rw [build_redraw, edit.eq_redraw ordered]
  refine ⟨?_, ?_, len, ?_⟩
  · obtain ⟨earlier, suffix, split, _⟩ := edit.flatten_split
    have mapEntries : map.entries = earlier ++ (key, planned.previous) :: suffix :=
      (build_entries profile.policy map).symm.trans split
    have before : ∀ entry ∈ earlier, key != entry.1 := by
      have sorted := map.ordered
      rw [mapEntries] at sorted
      intro entry hit
      have lt := (List.pairwise_append.mp sorted).2.2 entry hit (key, planned.previous) List.mem_cons_self
      simpa using (ne_of_lt lt).symm
    exact List.lookup_eq_some_iff.mpr ⟨earlier, suffix, mapEntries, before⟩
  · unfold RootProfile.rootName?
    rw [newTree]
    refine (Tree.rootName?_eq_some_iff _ _ _).mpr ⟨address, ?_, nextRoot.symm⟩
    intro block hit
    obtain ⟨v, b, enc, ser, hash, _⟩ := nextStored block hit
    simp [RootProfile.nameBlock?, enc, ser, hash, address]
  · rw [newTree]
    exact nextStored

theorem publish_succeeded [LinearOrder Key] [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) {observed authoritative staged : Name → Option ByteArray}
    {fuel : Nat} {root : Name} {key : Key} {value : Payload} {planned : Replacement Name Payload}
    (checked : profile.replaceValue reader observed authoritative fuel root key value = .ok (planned, staged)) :
    profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
        key value fuel none root = .ok planned ∧
      graph staged = union (graph authoritative) (listed planned.writes) := by
  cases plan : profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
      key value fuel none root with
  | error reason => simp [RootProfile.replaceValue, plan, Except.mapError, bind, Except.bind] at checked
  | ok result =>
    cases admitted : admit authoritative result.writes with
    | error name => simp [RootProfile.replaceValue, plan, admitted, Except.mapError, bind, Except.bind] at checked
    | ok updated =>
      simp [RootProfile.replaceValue, plan, admitted, Except.mapError, bind, Except.bind, pure, Except.pure] at checked
      obtain ⟨rfl, rfl⟩ := checked
      exact ⟨rfl, admit_eq_union admitted⟩

theorem collided [LinearOrder Key] [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) {observed authoritative : Name → Option ByteArray}
    {fuel : Nat} {root name : Name} {key : Key} {value : Payload}
    (checked : profile.replaceValue reader observed authoritative fuel root key value = .error (.collision name)) :
    ∃ planned, profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
        key value fuel none root = .ok planned ∧
      name ∈ collisions (union (graph authoritative) (listed planned.writes)) := by
  cases plan : profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
      key value fuel none root with
  | error reason => simp [RootProfile.replaceValue, plan, Except.mapError, bind, Except.bind] at checked
  | ok result =>
    cases admitted : admit authoritative result.writes with
    | error other =>
      simp [RootProfile.replaceValue, plan, admitted, Except.mapError, bind, Except.bind] at checked
      subst other
      exact ⟨result, rfl, by simpa only [admitted] using admit_spec authoritative result.writes⟩
    | ok updated =>
      simp [RootProfile.replaceValue, plan, admitted, Except.mapError, bind, Except.bind, pure, Except.pure] at checked

theorem publish_rebuild [LinearOrder Key] [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (map : OrderedMap Key Payload) {root : Name} (named : profile.rootName? map = some root)
    {observed authoritative staged : Name → Option ByteArray} (includes : Subset (graph observed) (graph authoritative))
    (present : Subset (profile.byteObservations (build profile.policy map)
      (replayAddress profile.nameBlock? root)) (graph authoritative))
    {fuel : Nat} {key : Key} {value : Payload} {planned : Replacement Name Payload}
    (checked : profile.replaceValue reader observed authoritative fuel root key value = .ok (planned, staged)) :
    let next := build profile.policy (replacedMap map key value)
    let address := replayAddress profile.nameBlock? root
    map.lookup? key = some planned.previous ∧ profile.rootName? (replacedMap map key value) = some planned.root ∧
      planned.writes.length = (build profile.policy map).level + 1 ∧
      profile.NodeBytes address (graph staged) next.level next.root ∧
      ∀ block ∈ blockOccurrences address next.level next.root, reader.readBlock? staged (address block) = some block := by
  obtain ⟨plan, stagedEq⟩ := publish_succeeded profile reader checked
  obtain ⟨previous, nextName, length, node⟩ := rebuild profile reader map named includes (graph_binding _) present plan
  rw [← stagedEq] at node
  refine ⟨previous, nextName, length, node, ?_⟩
  intro block hit
  obtain ⟨value, bytes, enc, ser, _, read⟩ := node block hit
  change staged _ = some bytes at read
  have recoverBlock := (blockCodec profile.key profile.payload).recovers (by simpa [blockCodec_encode] using enc)
  simp [Readback.readBlock?, read, reader.recovers ser, recoverBlock]

theorem absent_sound [LinearOrder Key] [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (map : OrderedMap Key Payload) {root : Name} (named : profile.rootName? map = some root)
    {observed authoritative : Name → Option ByteArray} {reference : Relation Name ByteArray}
    (includes : Subset (graph observed) reference) (bound : Binding reference)
    (present : Subset (profile.byteObservations (build profile.policy map)
      (replayAddress profile.nameBlock? root)) reference)
    {fuel : Nat} {key : Key} {value : Payload}
    (checked : profile.replaceValue reader observed authoritative fuel root key value = .error (.planning .absent)) :
    map.lookup? key = none := by
  let read := reader.pathReader observed
  let codec := blockCodec profile.key profile.payload
  let store : Store Name := ⟨project reference reader.decode?, fun _ _ => False⟩
  let tree := build profile.policy map
  let address := replayAddress profile.nameBlock? root
  have boundStore : store.Binding := ⟨bound.project _, fun _ _ _ no _ => False.elim no⟩
  have stored : Stored codec address tree store := by
    intro block hit
    obtain ⟨value, bytes, enc, ser, _, mem⟩ := storedNode profile map named present block hit
    exact ⟨value, by simpa [codec, blockCodec_encode] using enc, ⟨bytes, mem, reader.recovers ser⟩⟩
  have sound : Read.Sound read store := by
    intro name value hit
    cases seen : observed name with
    | none => simp [read, Readback.pathReader, seen] at hit
    | some bytes =>
      cases parsed : reader.decode? bytes with
      | none => simp [read, Readback.pathReader, seen, parsed] at hit
      | some found =>
        simp [read, Readback.pathReader, seen, parsed] at hit
        subst found
        exact ⟨bytes, includes seen, parsed⟩
  have absent : profile.planReplacement (readBlock codec read) key value fuel none root = .error .absent := by
    cases plan : profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
        key value fuel none root with
    | error reason =>
      have : reason = .absent := by
        simpa [RootProfile.replaceValue, plan, Except.mapError, bind, Except.bind] using checked
      rw [← this]
    | ok planned =>
      have impossible : (do
        let staged ← (admit authoritative planned.writes).mapError ReplaceError.collision
        pure (planned, staged)) = .error (.planning .absent) := by
        simpa [RootProfile.replaceValue, plan, Except.mapError, bind, Except.bind] using checked
      cases admitted : admit authoritative planned.writes <;>
        simp [admitted, Except.mapError, bind, Except.bind, pure, Except.pure] at impossible
  have routed : routedLookup codec read profile.policy.width fuel root key = .ok none :=
    plan_absent profile _ key value fuel none root absent
  rw [← (tree.replayAddress_spec _ root named).2] at routed
  have correct := routedLookup_sound (build_routable profile.policy map) stored boundStore sound routed
  simpa [OrderedMap.lookup?, tree] using correct

end Silmaril.Proofs.Formats.Dasl.ProllyReplace
