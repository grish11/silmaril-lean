module

public import Silmaril.Formats.Dasl.Arena.Prolly.Replace.Defs
public import Silmaril.Formats.Dasl.Prolly.Replace.Thms
import Silmaril.Formats.Dasl.Arena.Prolly.Index.Thms
import Silmaril.Semantics.Naming.Admission.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Replace

open Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Formats.Dasl.Arena.Prolly.Indexed
open Silmaril.Formats.Dasl.Prolly (Fault RootProfile readBlock blockCodec encodeBlock)
open Silmaril.Formats.Dasl.Prolly.RootProfile (PlanFailure Replacement patchFirst)
open Silmaril.Semantics.Prolly (Block selectChild)
open Silmaril.Semantics.Naming (Subset graph union listed admit)

variable {Name Key Payload : Type}

private def Agrees (arena : Indexed Name Key Payload) (profile : RootProfile Name Key Payload)
    (project : Handle Name → Name)
    (localPlan : Except (EditPlanError Name) (Indexed.Edit Name Key Payload))
    (namedPlan : Except (PlanFailure Name) (Replacement Name Payload)) : Prop :=
  match localPlan with
  | .ok edit =>
    namedPlan = .ok edit.named ∧
    edit.arena.blocks.size = arena.blocks.size + edit.named.writes.length ∧
    edit.root + 1 = edit.arena.blocks.size ∧
    (∀ index, index < arena.blocks.size → edit.arena.blocks[index]? = arena.blocks[index]?) ∧
    edit.PreservesNames arena.blocks.size project ∧ edit.project (.local edit.root) = edit.named.root ∧
    BlocksStaged profile arena.blocks.size edit.arena edit.project edit.named.writes
  | .error .absent => namedPlan = .error .absent
  | .error _ => True

private theorem pin_before {project : Handle Name → Name} {index : Nat} {name : Name}
    {ref : Handle Name} (live : KnownBefore index ref) : pin project index name ref = project ref := by
  cases ref with
  | «local» other => exact ite_eq_right (Nat.ne_of_lt live)
  | external _ => rfl

private theorem relabel_pin {project : Handle Name → Name} {index : Nat} {name : Name}
    {block : Block (Handle Name) Key Payload} (live : admissible index block = true) :
    relabel (pin project index name) block = relabel project block := by
  cases block with
  | leaf _ => rfl
  | branch level children =>
    simp only [relabel, Block.branch.injEq, true_and]
    exact List.map_congr_left fun child member => congrArg (Prod.mk child.1)
      (pin_before (admissible_iff.mp live child member))

private theorem admissible_widen {block : Block (Handle Name) Key Payload} {small large : Nat}
    (live : admissible small block = true) (order : small ≤ large) : admissible large block = true := by
  cases block with
  | leaf _ => rfl
  | branch level children =>
    apply admissible_iff.mpr
    intro child member
    have before := admissible_iff.mp live child member
    cases edge : child.2 with
    | «local» index => rw [edge] at before; exact Nat.lt_of_lt_of_le before order
    | external _ => trivial

private theorem copy_agrees {profile : RootProfile Name Key Payload} {project original : Handle Name → Name}
    {old : Nat} {arena : Indexed Name Key Payload} {block : Block (Handle Name) Key Payload}
    {oldName : Name} {previous : Payload} {writes : List (Name × ByteArray)}
    {base : Indexed Name Key Payload} (size : arena.blocks.size = base.blocks.size + writes.length)
    (frame : ∀ index, index < base.blocks.size → arena.blocks[index]? = base.blocks[index]?)
    (names : ∀ ref, KnownBefore base.blocks.size ref → project ref = original ref)
    (staged : BlocksStaged profile base.blocks.size arena project writes) :
    Agrees base profile original (copyBlock profile oldName project old arena block previous writes)
      (profile.emitReplacement oldName (relabel project block) previous writes) := by
  by_cases good : admissible arena.blocks.size block = true
  · cases result : profile.emitReplacement oldName (relabel project block) previous writes with
    | error reason => simp [copyBlock, Indexed.append?, good, result, Agrees]
    | ok plan =>
      have emitted : ∃ value bytes, encodeBlock profile.key profile.payload (relabel project block) = some value ∧
          profile.render? value = some bytes ∧ plan.writes = (plan.root, bytes) :: writes := by
        unfold RootProfile.emitReplacement at result
        split at result <;> try contradiction
        rename_i value encoded
        split at result <;> try contradiction
        rename_i bytes rendered
        split at result <;> try contradiction
        simp [pure, Except.pure] at result
        subst plan
        exact ⟨value, bytes, encoded, rendered, rfl⟩
      obtain ⟨value, bytes, encoded, rendered, batch⟩ := emitted
      have appended : arena.append? block = some (⟨arena.blocks.push block⟩, arena.blocks.size) := by
        simp [Indexed.append?, good]
      simp only [copyBlock, appended, result, Agrees, true_and]
      refine ⟨by simp [batch, size, Nat.add_assoc], by simp, ?_, ?_, by simp [pin], ?_⟩
      · intro index live
        rw [Array.getElem?_push_lt (by omega), ← getElem?_pos arena.blocks index (by omega), frame index live]
      · intro ref live
        apply Eq.trans (pin_before ?_) (names ref live)
        cases ref with
        | external _ => trivial
        | «local» index => exact Nat.lt_of_lt_of_le live (by omega)
      · intro index lower upper
        change index < (arena.blocks.push block).size at upper
        rw [Array.size_push] at upper
        by_cases last : index = arena.blocks.size
        · subst index
          refine ⟨block, value, bytes, Array.getElem?_push_size, good, ?_, rendered, ?_⟩
          · simpa only [relabel_pin good] using encoded
          · simp [pin, batch]
        · have earlier : index < arena.blocks.size := by omega
          obtain ⟨copied, shallow, raw, seen, backing, compiled, printed, member⟩ := staged index lower earlier
          refine ⟨copied, shallow, raw, ?_, backing, ?_, printed, ?_⟩
          · rw [Array.getElem?_push_lt earlier, ← getElem?_pos arena.blocks index earlier, seen]
          · simpa only [relabel_pin (admissible_widen backing (Nat.le_of_lt earlier))] using compiled
          · simp [pin, last, batch, member]
  · simp [copyBlock, Indexed.append?, good, Agrees]

set_option maxHeartbeats 600000 in
theorem plan [LinearOrder Key] (arena : Indexed Name Key Payload) (profile : RootProfile Name Key Payload)
    (project : Handle Name → Name) (read : Reader Name Key Payload)
    (key : Key) (value : Payload) (fuel : Nat) (expected : Option Nat) (ref : Handle Name)
    (agrees : PathAgrees arena project read key fuel ref) :
    match arena.planValue profile project key value fuel expected ref with
    | .ok edit =>
      profile.planReplacement read key value fuel expected (project ref) = .ok edit.named ∧
      edit.arena.blocks.size = arena.blocks.size + edit.named.writes.length ∧
      edit.root + 1 = edit.arena.blocks.size ∧
      (∀ index, index < arena.blocks.size → edit.arena.blocks[index]? = arena.blocks[index]?) ∧
      edit.PreservesNames arena.blocks.size project ∧ edit.project (.local edit.root) = edit.named.root ∧
      BlocksStaged profile arena.blocks.size edit.arena edit.project edit.named.writes
    | .error .absent => profile.planReplacement read key value fuel expected (project ref) = .error .absent
    | .error _ => True := by
  change Agrees arena profile project (arena.planValue profile project key value fuel expected ref)
    (profile.planReplacement read key value fuel expected (project ref))
  induction fuel generalizing expected ref with
  | zero => trivial
  | succ fuel ih =>
    cases ref with
    | external name => trivial
    | «local» index =>
      cases available : arena.blocks[index]? with
      | none => simp [planValue, available, Agrees]
      | some block =>
        obtain ⟨seen, childrenAgree⟩ := agrees block available
        cases block with
        | leaf entries =>
          simp only [planValue, available, RootProfile.planReplacement, seen, relabel, Except.mapError, bind,
            Except.bind]
          by_cases shape : (expected = none ∨ expected = some 0) ∧ entries.length ≤ profile.policy.width ∧
            entries.Pairwise (fun left right => left.1 < right.1)
          · rw [ite_eq_left shape, ite_eq_left shape]
            cases found : entries.lookup key with
            | none => rfl
            | some previous =>
              exact copy_agrees (writes := []) rfl (fun _ _ => rfl) (fun _ _ => rfl)
                (fun _ lower upper => False.elim (Nat.not_lt_of_ge lower upper))
          · simp [shape, Agrees]
        | branch level children =>
          let label : Key × Handle Name → Key × Name := fun child => (child.1, project child.2)
          have select : selectChild key (children.map label) = (selectChild key children).map label := by
            simp [selectChild, label, Function.comp_def]
          simp only [planValue, available, RootProfile.planReplacement, seen, relabel, Except.mapError, bind,
            Except.bind]
          by_cases live : admissible arena.blocks.size (.branch (Payload := Payload) level children) = true
          · simp only [live, Bool.not_true, Bool.false_eq_true, ite_false, List.length_map, List.pairwise_map]
            by_cases shape : (expected = none ∨ expected = some level) ∧ 0 < level ∧ 0 < children.length ∧
              children.length ≤ profile.policy.width ∧ children.Pairwise (fun left right => left.1 < right.1)
            · simp only [shape]
              change Agrees arena profile project _
                (match selectChild key (children.map label) with | none => _ | some _ => _)
              rw [select]
              cases found : selectChild key children with
              | none => rfl
              | some child =>
                simp only [Option.map_some]
                have below := ih (some (level - 1)) child.2 (childrenAgree child found)
                cases planned : arena.planValue profile project key value fuel (some (level - 1)) child.2 with
                | error err =>
                  rw [planned] at below
                  cases err <;> simp_all [Agrees, label]
                | ok edit =>
                  rw [planned] at below
                  obtain ⟨same, size, _, frame, names, rootName, staged⟩ :=
                    (show Agrees arena profile project (.ok edit) _ from below)
                  simp only [label, same]
                  have mapped : children.map (fun item => (item.1, edit.project item.2)) = children.map label :=
                    List.map_congr_left fun item member => congrArg (Prod.mk item.1)
                      (names _ (admissible_iff.mp live item member))
                  have commute : relabel edit.project (.branch (Payload := Payload) level
                      (patchFirst (fun entry => decide (key ≤ entry.1)) (child.1, .local edit.root) children)) =
                      .branch level (patchFirst (fun entry => decide (key ≤ entry.1)) (child.1, edit.named.root)
                        (children.map label)) := by
                    simp only [relabel, ← mapped, patchFirst, List.takeWhile_map,
                      List.dropWhile_map, List.map_append, List.map_cons, List.map_tail, Function.comp_def, rootName]
                  rw [← commute]
                  exact copy_agrees size frame names staged
            · simp [shape, Agrees]
          · simp [live, Agrees]

theorem admitted [LinearOrder Key] [DecidableEq Name] (arena : Indexed Name Key Payload)
    (profile : RootProfile Name Key Payload) (reader : profile.Readback) (project : Handle Name → Name)
    {observed authoritative staged : Name → Option ByteArray} {fuel root : Nat} {key : Key} {value : Payload}
    (agrees : PathAgrees arena project
      (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed)) key fuel (.local root))
    {edit : Indexed.Edit Name Key Payload}
    (replaced : arena.replaceValue profile project authoritative fuel root key value = .ok (edit, staged)) :
    profile.replaceValue reader observed authoritative fuel (project (.local root)) key value = .ok (edit.named, staged) ∧
      graph staged = union (graph authoritative) (listed edit.named.writes) ∧
      edit.arena.blocks.size = arena.blocks.size + edit.named.writes.length ∧
      edit.root + 1 = edit.arena.blocks.size ∧
      (∀ index, index < arena.blocks.size → edit.arena.blocks[index]? = arena.blocks[index]?) ∧
      edit.PreservesNames arena.blocks.size project ∧ edit.project (.local edit.root) = edit.named.root ∧
      BlocksStaged profile arena.blocks.size edit.arena edit.project edit.named.writes := by
  unfold Indexed.replaceValue at replaced
  cases planned : arena.planValue profile project key value fuel none (.local root) with
  | error reason => simp [planned, Except.mapError, bind, Except.bind] at replaced
  | ok result =>
    cases accepted : admit authoritative result.named.writes with
    | error name => simp [planned, accepted, Except.mapError, bind, Except.bind] at replaced
    | ok updated =>
      simp [planned, accepted, Except.mapError, bind, Except.bind, pure, Except.pure] at replaced
      obtain ⟨rfl, rfl⟩ := replaced
      have spec := plan arena profile project _ key value fuel none (.local root) agrees
      rw [planned] at spec
      obtain ⟨same, size, last, frame⟩ := spec
      refine ⟨?_, Silmaril.Semantics.Naming.admit_eq_union accepted, size, last, frame⟩
      simp [RootProfile.replaceValue, same, accepted, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem collided [LinearOrder Key] [DecidableEq Name] (arena : Indexed Name Key Payload)
    (profile : RootProfile Name Key Payload) (project : Handle Name → Name)
    {authoritative : Name → Option ByteArray} {fuel root : Nat} {key : Key} {value : Payload} {name : Name}
    (rejected : arena.replaceValue profile project authoritative fuel root key value = .error (.collision name)) :
    ∃ edit, arena.planValue profile project key value fuel none (.local root) = .ok edit ∧
      name ∈ Silmaril.Semantics.Naming.collisions (union (graph authoritative) (listed edit.named.writes)) := by
  cases staged : arena.planValue profile project key value fuel none (.local root) with
  | error reason => simp [Indexed.replaceValue, staged, Except.mapError, bind, Except.bind] at rejected
  | ok edit =>
    cases accepted : admit authoritative edit.named.writes with
    | ok updated => simp [Indexed.replaceValue, staged, accepted, Except.mapError, bind, Except.bind,
        pure, Except.pure] at rejected
    | error conflict =>
      simp [Indexed.replaceValue, staged, accepted, Except.mapError, bind, Except.bind] at rejected
      subst conflict
      have spec := Silmaril.Semantics.Naming.admit_spec authoritative edit.named.writes
      exact ⟨edit, rfl, by simpa only [accepted] using spec⟩

theorem absent [LinearOrder Key] [DecidableEq Name] (arena : Indexed Name Key Payload)
    (profile : RootProfile Name Key Payload) (reader : profile.Readback) (project : Handle Name → Name)
    {observed authoritative : Name → Option ByteArray} {fuel root : Nat} {key : Key} {value : Payload}
    (agrees : PathAgrees arena project
      (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed)) key fuel (.local root))
    (rejected : arena.replaceValue profile project authoritative fuel root key value = .error (.planning .absent)) :
    profile.replaceValue reader observed authoritative fuel (project (.local root)) key value =
      .error (.planning .absent) := by
  cases planned : arena.planValue profile project key value fuel none (.local root) with
  | error reason =>
    simp [Indexed.replaceValue, planned, Except.mapError, bind, Except.bind] at rejected
    subst reason
    have spec := plan arena profile project _ key value fuel none (.local root) agrees
    rw [planned] at spec
    simp [RootProfile.replaceValue, spec, Except.mapError, bind, Except.bind]
  | ok edit =>
    cases accepted : admit authoritative edit.named.writes <;>
      simp [Indexed.replaceValue, planned, accepted, Except.mapError, bind, Except.bind, pure, Except.pure] at rejected

theorem readback {profile : RootProfile Name Key Payload} (reader : profile.Readback)
    {base : Nat} {arena : Indexed Name Key Payload} {project : Handle Name → Name}
    {writes : List (Name × ByteArray)} {staged : Name → Option ByteArray}
    (covered : BlocksStaged profile base arena project writes) (includes : Subset (listed writes) (graph staged))
    {index : Nat} (lower : base ≤ index) (upper : index < arena.blocks.size) :
    ∃ block, arena.blocks[index]? = some block ∧
      reader.readBlock? staged (project (.local index)) = some (relabel project block) := by
  obtain ⟨block, value, bytes, stored, _, encoded, rendered, member⟩ := covered index lower upper
  have present : staged (project (.local index)) = some bytes := includes member
  have decoded := (blockCodec profile.key profile.payload).recovers
    (by simpa [Silmaril.Formats.Dasl.Prolly.blockCodec_encode] using encoded)
  exact ⟨block, stored, by simp [RootProfile.Readback.readBlock?, present, reader.recovers rendered, decoded]⟩

theorem rebuilt [LinearOrder Key] [DecidableEq Name] (arena : Indexed Name Key Payload)
    (profile : RootProfile Name Key Payload) (reader : profile.Readback) (project : Handle Name → Name)
    (map : Silmaril.Semantics.OrderedMap Key Payload)
    {observed authoritative staged : Name → Option ByteArray} {fuel root : Nat} {key : Key} {value : Payload}
    {edit : Indexed.Edit Name Key Payload}
    (named : profile.rootName? map = some (project (.local root)))
    (agrees : PathAgrees arena project
      (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed)) key fuel (.local root))
    (includes : Subset (graph observed) (graph authoritative))
    (present : Subset (profile.byteObservations (Semantics.Prolly.build profile.policy map)
      (Semantics.Prolly.replayAddress profile.nameBlock? (project (.local root)))) (graph authoritative))
    (replaced : arena.replaceValue profile project authoritative fuel root key value = .ok (edit, staged)) :
    let next := Semantics.Prolly.build profile.policy (RootProfile.replacedMap map key value)
    let address := Semantics.Prolly.replayAddress profile.nameBlock? (project (.local root))
    map.lookup? key = some edit.named.previous ∧
    profile.rootName? (RootProfile.replacedMap map key value) = some (edit.project (.local edit.root)) ∧
    edit.arena.blocks.size = arena.blocks.size + (Semantics.Prolly.build profile.policy map).level + 1 ∧
    ∀ block ∈ Semantics.Prolly.blockOccurrences address next.level next.root,
      reader.readBlock? staged (address block) = some block := by
  obtain ⟨same, _, size, _, _, _, rootName, _⟩ := admitted arena profile reader project agrees replaced
  obtain ⟨previous, canonical, count, _, reads⟩ := profile.replaceValue_rebuild reader map named includes present same
  exact ⟨previous, rootName ▸ canonical, by rw [size, count, Nat.add_assoc], reads⟩

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Replace
