module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Publication
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Selection
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Frame
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Loader (Manifest ModuleId Session)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (Cell State)
local notation "ImportFrame" => Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Frame

@[expose] def KeepsBelow (floor : Nat) (before after : State) : Prop :=
  ∀ address cell, address < floor → before.heap[address]? = some cell →
    ∃ flag, after.heap[address]? = some {cell with frozen := flag}

theorem below_trans {floor : Nat} {before middle after : State}
    (first : KeepsBelow floor before middle) (second : KeepsBelow floor middle after) :
    KeepsBelow floor before after := by
  intro address cell small found
  obtain ⟨flag, stored⟩ := first address cell small found
  exact second address {cell with frozen := flag} small stored

private theorem blank_after {before after : State} {binding : Binding}
    (slots : after.slots = before.slots) (contents : KeepsContents before after)
    (blank : Blank before binding) : Blank after binding := by
  obtain ⟨address, flag, owned, stored⟩ := blank
  obtain ⟨frozen, next⟩ := contents address ⟨.binding none, flag⟩ stored
  exact ⟨address, frozen, slots ▸ owned, next⟩

private theorem frame_after {aliases globals : List String} {before after : State}
    (slots : after.slots = before.slots) (contents : KeepsContents before after)
    (frame : ImportFrame aliases globals before) : ImportFrame aliases globals after := by
  refine ⟨?_, ?_⟩
  · intro first second address atFirst atSecond
    exact frame.1 _ _ _ (slots.symm ▸ atFirst) (slots.symm ▸ atSecond)
  · intro binding member
    obtain ⟨address, value, flag, owned, stored⟩ := frame.2 binding member
    obtain ⟨frozen, next⟩ := contents address ⟨.binding value, flag⟩ stored
    exact ⟨address, value, frozen, slots ▸ owned, next⟩

private theorem live_after {aliases : List String} {origin program : Program} {env : Tracked} {before after : State}
    (slots : after.slots = before.slots) (contents : KeepsContents before after)
    (live : Live aliases origin program env before) : Live aliases origin program env after := by
  intro name callee tracked
  obtain ⟨slot, address, flag, owned, stored, record⟩ := live name callee tracked
  obtain ⟨frozen, next⟩ := contents slot ⟨.binding (some (.function address)), flag⟩ stored
  exact ⟨slot, address, frozen, slots ▸ owned, next, transport_callable record (closure_cells_of_contents contents)⟩

private structure Committed (aliases globals : List String) (origin program : Program)
    (env : Tracked) (floor : Nat) (reserved : List Binding) (before after : State) : Prop where
  slots : after.slots = before.slots
  contents : KeepsBelow floor before after
  records : KeepsClosureCells before after
  frame : ImportFrame aliases globals after
  live : Live aliases origin program env after
  untouched : ∀ binding ∈ reserved, Blank after binding

/-- Installation starts only after selection and writes the selected references
into distinct blank cells, preserving the earlier live closures. -/
private theorem commit {origin program : Program} {state : State} {items : List ImportBinding}
    {env final : Tracked} {entries : List (Binding × Lists.Value)}
    (chosen : SelectedValues origin program state items env entries final)
    {aliases globals : List String} {reserved : List Binding} {floor : Nat}
    (visible : ∀ name ∈ items.map ImportBinding.alias, name ∈ aliases)
    (unique : (items.map ImportBinding.alias).Nodup)
    (disjoint : ∀ name ∈ items.map ImportBinding.alias, fileSlot name ∉ reserved)
    (frame : ImportFrame aliases globals state) (fresh : FreshSlots floor state)
    (live : Live aliases origin program env state)
    (pending : ∀ name ∈ items.map ImportBinding.alias, Blank state (fileSlot name))
    (untouched : ∀ binding ∈ reserved, Blank state binding) :
    Committed aliases globals origin program final floor reserved state (installImports state entries) := by
  induction items generalizing state env entries with
  | nil =>
    cases chosen
    exact ⟨rfl, fun _ cell _ stored => ⟨cell.frozen, stored⟩,
      closure_cells_of_contents (keeps_contents_refl _), frame, live, untouched⟩
  | cons item rest ih =>
    cases chosen with
    | @next _ _ _ _ callee address entries record remaining =>
      let value := Lists.Value.function address
      let next := state.write (fileSlot item.alias) value
      have blank := pending item.alias List.mem_cons_self
      have atAlias : readSlot aliases item.alias = fileSlot item.alias := by
        simp [readSlot, visible item.alias List.mem_cons_self]
      have nextLive : Live aliases origin program (track env item.alias (some callee)) next := by
        exact Eq.mp (congrArg (fun target => Live aliases origin program (track env item.alias (some callee))
          (state.write target value)) atAlias)
          (write_tracked (atAlias.symm ▸ blank) live value (some callee)
            (fun target same => by cases same; exact ⟨address, rfl, record⟩))
      have nextSlots : next.slots = state.slots := write_slots _ _ _
      have nextRecords := write_blank_cells blank value
      have nextPending : ∀ name ∈ rest.map ImportBinding.alias, Blank next (fileSlot name) := by
        intro name member
        apply other_blank frame.1 _ (pending name (List.mem_cons_of_mem _ member)) value
        intro same
        have sameName : item.alias = name := congrArg Binding.name same
        exact (List.nodup_cons.mp unique).1 (sameName ▸ member)
      have after := ih (selected_transport remaining nextRecords)
        (fun name member => visible name (List.mem_cons_of_mem _ member))
        (List.nodup_cons.mp unique).2
        (fun name member => disjoint name (List.mem_cons_of_mem _ member))
        (writes_frame frame (fileSlot item.alias) value)
        (fun binding slot owned => fresh binding slot (nextSlots ▸ owned))
        nextLive nextPending (fun binding member =>
          other_blank (writable := fileSlot item.alias) frame.1
            (fun same => disjoint item.alias List.mem_cons_self (same ▸ member)) (untouched binding member) value)
      obtain ⟨slot, _, owned, _⟩ := blank
      have writeKeeps := write_keeps_below owned (fresh _ _ owned) value
      exact ⟨after.slots.trans nextSlots,
        below_trans (fun _ cell small stored => ⟨cell.frozen, writeKeeps.2 _ _ small stored⟩) after.contents,
        closure_cells_trans nextRecords after.records, after.frame, after.live, after.untouched⟩


/-- The reached prefix keeps previously published modules and protects cells
outside the importer frame. Success establishes the suite's entry invariant. -/
structure PrefixReached (origin program : Program) (manifest : Manifest) (exports : ModuleId → Tracked)
    (aliases globals : List String) (floor : Nat) (reserved : List Binding) (final : Option Tracked)
    (caller : Session) (out : Modules.Loader.Result Unit) : Prop where
  slots : (resultSession out).runtime.slots = caller.runtime.slots
  contents : KeepsBelow floor caller.runtime (resultSession out).runtime
  cache : Cache origin program manifest exports (resultSession out)
  retained : ∀ id value, caller.cache.lookup id = some value → (resultSession out).cache.lookup id = some value
  ready : ∀ next, out = .ok () next →
    ∃ env, final = some env ∧ ImportFrame aliases globals next.runtime ∧ Live aliases origin program env next.runtime ∧
      ∀ binding ∈ reserved, Blank next.runtime binding

/-- The continuation receives only a successful prefix. An error leaves the
remaining load commands and any body suffix unreachable. -/
@[expose] def Continues (program : Program) (manifest : Manifest) (active : List ModuleId) (id : ModuleId)
    (suffix : List Modules.Command) (prefixOut out : Modules.Loader.Result Unit) : Prop :=
  match prefixOut with
  | .ok () reached => Modules.Loader.Runs program manifest active (.commands id suffix) reached out
  | .error error reached => out = .error error reached

theorem run_prefix {origin program : Program} {manifest : Manifest} {exports : ModuleId → Tracked}
    {id : ModuleId} {bound : id < manifest.size} {active : List ModuleId}
    (loadEarlier : ∀ dependency, dependency < id → ∀ session,
      Cache origin program manifest exports session →
      ∃ out, TraceRun manifest dependency session out ∧
        Modules.Loader.Runs program manifest active (.initialize dependency) session out ∧
        Reached origin program manifest exports dependency session out)
    {imports : List ImportSite} {env : Tracked} {final : Option Tracked}
    (plan : ImportPlan manifest exports id bound imports env final)
    {aliases globals : List String} {floor : Nat} {reserved : List Binding}
    (visible : ∀ name ∈ imports.flatMap ImportSite.aliases, name ∈ aliases)
    (unique : (imports.flatMap ImportSite.aliases).Nodup)
    (disjoint : ∀ name ∈ imports.flatMap ImportSite.aliases, fileSlot name ∉ reserved)
    (caller : Session) (cache : Cache origin program manifest exports caller)
    (frame : ImportFrame aliases globals caller.runtime) (fresh : FreshSlots floor caller.runtime)
    (live : Live aliases origin program env caller.runtime)
    (pending : ∀ name ∈ imports.flatMap ImportSite.aliases, Blank caller.runtime (fileSlot name))
    (untouched : ∀ binding ∈ reserved, Blank caller.runtime binding) :
    ∃ out, ImportTrace manifest id imports caller out ∧
      (∀ suffix result, Continues program manifest active id suffix out result →
        Modules.Loader.Runs program manifest active (.commands id (imports.map ImportSite.code ++ suffix)) caller result) ∧
      PrefixReached origin program manifest exports aliases globals floor reserved final caller out := by
  induction plan generalizing caller with
  | done env =>
    exact ⟨_, .done caller, fun _ _ rest => rest, ⟨rfl, fun _ cell _ stored => ⟨cell.frozen, stored⟩, cache,
      fun _ _ old => old, fun _ same => by cases same; exact ⟨env, rfl, frame, live, untouched⟩⟩⟩
  | unresolved label =>
    refine ⟨_, .unresolved label, ?_, ⟨rfl, fun _ cell _ stored => ⟨cell.frozen, stored⟩, cache,
      fun _ _ old => old, fun _ impossible => nomatch impossible⟩⟩
    intro suffix result rest
    cases rest
    exact .failed (.missingLabel label)
  | @load site tail env dependency selected final earlier label sourceSelection _ _ ih =>
    obtain ⟨loaded, trace, native, reached⟩ := loadEarlier dependency earlier caller cache
    cases loaded with
    | error error stopped =>
      refine ⟨_, .dependencyError label trace, ?_, ⟨reached.slots, fun _ _ _ => reached.contents _ _,
        reached.cache, reached.retained, fun _ impossible => nomatch impossible⟩⟩
      intro suffix result rest
      cases rest
      exact .failed (.loadFailed label native)
    | ok published stopped =>
      obtain ⟨_, actual⟩ := reached.cache dependency published (reached.published _ _ rfl)
      obtain ⟨selection, lookup, matched⟩ := select_covered actual sourceSelection site.label
      have runLoad : Modules.Loader.Runs program manifest active (.command id site.code) caller
          (Modules.Loader.liftResult id stopped (Modules.bindImports selection stopped.runtime)) := by
        rw [← group_agrees (site := site) lookup]
        exact .load label native
      cases selection with
      | error error =>
        refine ⟨_, .selectionError label trace lookup, ?_, ⟨reached.slots, fun _ _ _ => reached.contents _ _,
          reached.cache, reached.retained, fun _ impossible => nomatch impossible⟩⟩
        intro suffix result rest
        cases rest
        exact .failed runLoad
      | ok entries =>
        cases selected with
        | none => exact False.elim matched
        | some next =>
          let tailAliases := tail.flatMap ImportSite.aliases
          have distinct : (site.aliases ++ tailAliases).Nodup := unique
          obtain ⟨groupUnique, tailUnique, separates⟩ := List.pairwise_append.mp distinct
          have orderedAlias : site.bindings.reverse.map ImportBinding.alias = site.aliases.reverse :=
            List.map_reverse
          have groupMember {name : String} (member : name ∈ site.bindings.reverse.map ImportBinding.alias) :
              name ∈ (site :: tail).flatMap ImportSite.aliases := by
            rw [orderedAlias, List.mem_reverse] at member
            exact List.mem_append.mpr (.inl member)
          have tailMember {name : String} (member : name ∈ tailAliases) :
              name ∈ (site :: tail).flatMap ImportSite.aliases :=
            List.mem_append.mpr (.inr member)
          have reservedBlank (binding : Binding) (member : binding ∈ tailAliases.map fileSlot ++ reserved) :
              Blank stopped.runtime binding := by
            apply blank_after reached.slots reached.contents
            rcases List.mem_append.mp member with earlierAlias | reservedMember
            · obtain ⟨name, member, same⟩ := List.mem_map.mp earlierAlias
              exact same ▸ pending name (tailMember member)
            · exact untouched binding reservedMember
          have separateReserved (name : String) (member : name ∈ site.bindings.reverse.map ImportBinding.alias) :
              fileSlot name ∉ tailAliases.map fileSlot ++ reserved := by
            rw [orderedAlias, List.mem_reverse] at member
            intro conflict
            rcases List.mem_append.mp conflict with aliasConflict | reservedConflict
            · obtain ⟨other, inTail, same⟩ := List.mem_map.mp aliasConflict
              exact separates name member other inTail ((congrArg Binding.name same).symm)
            · exact disjoint name (List.mem_append.mpr (.inl member)) reservedConflict
          let bound := {stopped with runtime := installImports stopped.runtime entries}
          have committed := commit matched (fun _ member => visible _ (groupMember member))
            (by rw [orderedAlias, List.Nodup, List.pairwise_reverse]; exact groupUnique.imp Ne.symm) separateReserved
            (frame_after reached.slots reached.contents frame)
            (fun binding slot owned => fresh binding slot (reached.slots ▸ owned))
            (live_after reached.slots reached.contents live)
            (fun name member => blank_after reached.slots reached.contents (pending name (groupMember member)))
            reservedBlank
          have boundSlots : bound.runtime.slots = caller.runtime.slots := committed.slots.trans reached.slots
          have boundCache := cache_transport (next := bound) reached.cache committed.records rfl
          obtain ⟨out, tailTrace, tailNative, after⟩ := ih next rfl
            (fun name member => visible _ (tailMember member)) tailUnique
            (fun name member => disjoint _ (tailMember member)) bound boundCache committed.frame
            (fun binding slot owned => fresh binding slot (boundSlots ▸ owned)) committed.live
            (fun name member => committed.untouched _ (List.mem_append.mpr (.inl (List.mem_map_of_mem member))))
            (fun binding member => committed.untouched _ (List.mem_append.mpr (.inr member)))
          have step : Modules.Loader.Runs program manifest active (.command id site.code) caller (.ok () bound) :=
            runLoad
          have kept : KeepsBelow floor caller.runtime bound.runtime :=
            below_trans (fun _ _ _ => reached.contents _ _) committed.contents
          refine ⟨out, .next label trace lookup tailTrace,
            fun suffix result rest => .step step (tailNative suffix result rest),
            ⟨after.slots.trans boundSlots, below_trans kept after.contents, after.cache, ?_, after.ready⟩⟩
          exact fun index publication old => after.retained index publication (reached.retained index publication old)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
