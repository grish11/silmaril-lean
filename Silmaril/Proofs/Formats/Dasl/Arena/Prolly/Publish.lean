module

public import Silmaril.Formats.Dasl.Arena.Prolly.Publish.Defs
import Silmaril.Semantics.Naming.Admission.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Publish

open Silmaril.Formats.Dasl.Arena.Prolly
open Silmaril.Formats.Dasl.Arena.Prolly.Publish
open Silmaril.Formats.Dasl.Prolly (RootProfile blockCodec blockCodec_encode)
open Silmaril.Semantics.Naming (admit admit_eq_union admit_spec collisions graph listed union)
open Silmaril.Semantics.Prolly (Block)

variable {Name Key Payload : Type} {profile : RootProfile Name Key Payload}

private theorem pack_name (block : Block Name Key Payload) :
    (pack profile block).map Packed.name = profile.nameBlock? block := by
  unfold pack RootProfile.nameBlock?
  split
  · simp_all
  · split
    · simp_all
    · split <;> simp_all

private theorem option_mapM_project {Item Input Output : Type} (items : List Item) (fetch : Item → Option Input)
    (project : Input → Output) : (items.mapM fetch).map (List.map project) = items.mapM fun item => (fetch item).map project := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.mapM_cons]
    cases got : fetch head with
    | none => rfl
    | some value =>
      simp only [Option.map_some, Bind.bind, Option.bind]
      cases rest : tail.mapM fetch with
      | none => simp [rest] at ih; simp [← ih]
      | some values => simp [rest] at ih; simp [← ih]

theorem stage_name (arena : Indexed Name Key Payload) (fuel : Nat) (ref : Handle Name) :
    (stage arena profile fuel ref).map Plan.root = arena.name? profile.nameBlock? fuel ref := by
  induction fuel generalizing ref with
  | zero => cases ref <;> rfl
  | succ fuel ih =>
    cases ref with
    | external name => rfl
    | «local» index =>
      cases stored : arena.blocks[index]? with
      | none => simp [stage, Indexed.name?, stored, Bind.bind, Option.bind]
      | some block =>
        cases block with
        | leaf entries =>
          simp only [stage, Indexed.name?, stored, Bind.bind, Option.bind]
          rw [← pack_name]
          cases pack profile (.leaf entries) <;> rfl
        | branch level children =>
          let fetch := fun (pair : Key × Handle Name) => (stage arena profile fuel pair.2).map (pair.1, ·)
          let names := fun (pair : Key × Plan profile) => (pair.1, pair.2.root)
          have named : (children.mapM fetch).map (List.map names) =
              children.mapM fun (key, child) => (arena.name? profile.nameBlock? fuel child).map (key, ·) := by
            rw [option_mapM_project]
            congr 1
            funext pair
            simp [fetch, names, Option.map_map, Function.comp_def, ← ih pair.2]
          simp only [stage, Indexed.name?, stored, Bind.bind, Option.bind]
          change (do
            let groups ← children.mapM fetch
            let packed ← pack profile (.branch level (groups.map names))
            pure (⟨packed.name, (groups.flatMap fun (pair : Key × Plan profile) => pair.2.blocks) ++ [packed]⟩ : Plan profile)).map Plan.root = _
          rw [← named]
          cases staged : children.mapM fetch with
          | none => rfl
          | some groups =>
            change _ = profile.nameBlock? (.branch level (groups.map names))
            rw [← pack_name]
            simp only [Bind.bind, Option.bind]
            cases pack profile (.branch level (groups.map names)) <;> rfl

theorem stage_root_packed (arena : Indexed Name Key Payload) {fuel index : Nat} {plan : Plan profile}
    (staged : stage arena profile fuel (.local index) = some plan) :
    ∃ packed ∈ plan.blocks, packed.name = plan.root := by
  cases fuel with
  | zero => simp [stage] at staged
  | succ fuel =>
    cases stored : arena.blocks[index]? with
    | none => simp [stage, stored, Bind.bind, Option.bind] at staged
    | some block =>
      cases block with
      | leaf entries =>
        cases packed : pack profile (.leaf entries) with
        | none => simp [stage, stored, packed, Bind.bind, Option.bind] at staged
        | some found =>
          have eq : (⟨found.name, [found]⟩ : Plan profile) = plan := by
            simpa [stage, stored, packed, Bind.bind, Option.bind, Pure.pure] using staged
          subst plan
          exact ⟨found, by simp, rfl⟩
      | branch level children =>
        let fetch := fun (pair : Key × Handle Name) => (stage arena profile fuel pair.2).map (pair.1, ·)
        cases named : children.mapM fetch with
        | none =>
          simp [stage, stored, Bind.bind, Option.bind] at staged
          change (children.mapM fetch).bind _ = _ at staged
          simp [named] at staged
        | some groups =>
          simp only [stage, stored, Bind.bind, Option.bind] at staged
          change (children.mapM fetch).bind _ = _ at staged
          rw [named] at staged
          cases packed : pack profile (.branch level (groups.map fun (key, plan) => (key, plan.root))) with
          | none => simp [packed, Option.bind] at staged
          | some found =>
            have eq : (⟨found.name, (groups.flatMap fun pair => pair.2.blocks) ++ [found]⟩ : Plan profile) = plan := by
              simpa [packed, Option.bind, Pure.pure] using staged
            subst plan
            exact ⟨found, by simp, rfl⟩

theorem packed_readback (reader : profile.Readback) (packed : Packed profile) {read : Name → Option ByteArray}
    (present : read packed.name = some packed.bytes) : reader.readBlock? read packed.name = some packed.block := by
  have decoded := (blockCodec profile.key profile.payload).recovers (by
    rw [blockCodec_encode]; exact packed.encoded)
  simp [RootProfile.Readback.readBlock?, present, reader.recovers packed.rendered, decoded]

theorem publish_spec [DecidableEq Name] (arena : Indexed Name Key Payload) (reader : profile.Readback)
    (read : Name → Option ByteArray) {fuel index : Nat} {plan : Plan profile}
    (staged : stage arena profile fuel (.local index) = some plan) :
    match publish arena profile fuel index read with
    | .ok (name, updated) => name = plan.root ∧ graph updated = union (graph read) (listed plan.writes) ∧
        ∀ packed ∈ plan.blocks, reader.readBlock? updated packed.name = some packed.block
    | .error (.collision name) => name ∈ collisions (union (graph read) (listed plan.writes))
    | .error .naming => False := by
  unfold publish
  rw [staged]
  cases observed : admit read plan.writes with
  | error name => simpa [observed, Except.map, Except.mapError] using admit_spec read plan.writes
  | ok updated =>
    simp only [observed, Except.map, Except.mapError, true_and]
    have exactUnion := admit_eq_union observed
    refine ⟨exactUnion, fun packed hit => packed_readback reader packed ?_⟩
    change graph updated packed.name packed.bytes
    rw [exactUnion]
    exact Or.inr (List.mem_map_of_mem hit)

end Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Publish
