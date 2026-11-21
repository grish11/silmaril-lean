module

public import Silmaril.Formats.Git.Translate.Thms

/-! Rooted discovery from a typed partial store. Local dependencies are followed;
gitlinks are an explicit boundary, independent of whether a local binding exists. -/

@[expose] public section

namespace Silmaril.Formats.Git.Translate.Graph

open Silmaril.Semantics

variable {Key Source Target Meta : Type} {algorithm : Native.Algorithm}

inductive Role : Kind → Type where
  | local {kind : Kind} : Role kind
  | gitlink : Role .commit

def roleFor : (mode : EntryMode) → Role mode.kind
  | .gitlink => .gitlink
  | .directory | .file _ => .local

structure Edge (Source : Type) where
  kind : Kind
  source : Source
  role : Role kind

abbrev Address (Source : Type) := Kind × Source

inductive Node (Key Source : Type) : Kind → Type where
  | blob (payload : ByteArray) : Node Key Source .blob
  | tree (entries : ShallowTree Key Source) : Node Key Source .tree
  | commit (data : Commit Source Source Native.CommitMetadata) : Node Key Source .commit

abbrev Node.Index : {kind : Kind} → Node Key Source kind → Type
  | _, .blob _ => Empty
  | _, .tree entries => ↥entries.keys
  | _, .commit data => Option (Fin data.parents.length)

abbrev Node.edge : {kind : Kind} → (node : Node Key Source kind) → node.Index → Edge Source
  | _, .blob _, index => index.elim
  | _, .tree entries, index =>
    let entry := entries.get index
    ⟨entry.mode.kind, entry.target, roleFor entry.mode⟩
  | _, .commit data, none => ⟨.tree, data.tree, .local⟩
  | _, .commit data, some index => ⟨.commit, data.parents.get index, .local⟩

instance [DecidableEq Key] {kind : Kind} (node : Node Key Source kind) : DecidableEq node.Index :=
  match node with
  | .blob _ => inferInstanceAs (DecidableEq Empty)
  | .tree entries => inferInstanceAs (DecidableEq ↥entries.keys)
  | .commit data => inferInstanceAs (DecidableEq (Option (Fin data.parents.length)))

def Node.indices [LinearOrder Key] : {kind : Kind} → (node : Node Key Source kind) → List node.Index
  | _, .blob _ => []
  | _, .tree entries => entries.keys.sort.attach.map (fun key => ⟨key.val, (Finset.mem_sort _).mp key.property⟩)
  | _, .commit data => none :: (List.finRange data.parents.length).map some

theorem Node.mem_indices [LinearOrder Key] {kind : Kind} (node : Node Key Source kind) (index : node.Index) :
    index ∈ node.indices := by
  cases node with
  | blob => exact index.elim
  | tree entries => exact List.mem_map.mpr ⟨⟨index.val, (Finset.mem_sort _).mpr index.property⟩, by simp, rfl⟩
  | commit data =>
    cases index with
    | none => exact List.mem_cons_self
    | some index => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨index, List.mem_ofFn.mpr ⟨index, rfl⟩, rfl⟩)

def Node.expand : {kind : Kind} → (node : Node Key Source kind) →
    ((index : node.Index) → Object Key Source Native.CommitMetadata (node.edge index).kind) →
    Object Key Source Native.CommitMetadata kind
  | _, .blob bytes, _ => .blob bytes
  | _, .tree entries, children => .tree entries.keys (fun index => (entries.get index).mode) children
  | _, .commit data, children => .commit (children none) _ (fun index => children (some index)) data.metadata

def Node.preimage? (native : Native.Profile algorithm Key Source) : {kind : Kind} → Node Key Source kind → Option ByteArray
  | _, .blob payload => some (Native.loose .blob payload)
  | _, .tree entries => (Native.treePayload? native.names (entries.rekey native.key)).map (Native.loose .tree)
  | _, .commit data => Native.commitBytes? native.names data

structure Binding (Key Source : Type) (kind : Kind) where
  node : Node Key Source kind
  bytes : ByteArray

/-- `invalid` comes from the adapter (e.g. bad bytes or wrong object kind);
the traversal separately checks reserialization and the requested name. -/
inductive Read (Value : Type) where
  | missing | invalid | found (value : Value)

abbrev Lookup (Key Source : Type) := (kind : Kind) → Source → Read (Binding Key Source kind)

def Lookup.observed (lookup : Lookup Key Source) (kind : Kind) : Naming.Relation Source ByteArray :=
  fun source bytes => (match lookup kind source with | .found data => some data.bytes | _ => none) = some bytes

def Binding.valid (native : Native.Profile algorithm Key Source) {kind : Kind}
    (binding : Binding Key Source kind) (source : Source) : Prop :=
  binding.node.preimage? native = some binding.bytes ∧ native.assign binding.bytes = source

instance [DecidableEq Source] (native : Native.Profile algorithm Key Source) {kind : Kind}
    (binding : Binding Key Source kind) (source : Source) : Decidable (binding.valid native source) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A finite certificate with all local edges and ordered parent slots present.
Every local node is the binding returned at its typed name. A gitlink contributes
only a reference, not a claim about the other repository's objects. -/
inductive Plan (native : Native.Profile algorithm Key Source) (lookup : Lookup Key Source) :
    {kind : Kind} → Role kind → Source → Type where
  | external (source : Source) : Plan native lookup .gitlink source
  | found {kind : Kind} (source : Source) (binding : Binding Key Source kind)
      (read : lookup kind source = .found binding) (valid : binding.valid native source)
      (children : (index : binding.node.Index) →
        Plan native lookup (binding.node.edge index).role (binding.node.edge index).source) :
      Plan native lookup (.local (kind := kind)) source

def Plan.expand {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source} :
    {kind : Kind} → {role : Role kind} → {source : Source} →
    Plan native lookup role source → Object Key Source Native.CommitMetadata kind
  | _, _, _, .external source => .ref .commit source
  | _, _, _, .found _ binding _ _ children => binding.node.expand (fun index => (children index).expand)

def Plan.expected {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source} :
    {kind : Kind} → {role : Role kind} → {source : Source} → Plan native lookup role source → Native.View Source
  | _, _, _, .external source => .opaque source
  | _, _, _, .found _ binding _ _ _ => .encoded binding.bytes

theorem Plan.expectedName {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    {kind : Kind} {role : Role kind} {source : Source} (plan : Plan native lookup role source) :
    plan.expected.target native.assign = source := by
  cases plan with | external => rfl | found _ _ _ valid _ => exact valid.2

inductive Error (Source : Type) where
  | missing (address : Address Source)
  | invalid (address : Address Source)
  | cycle (address : Address Source)
  | fuel (address : Address Source)
  | externalGitlink (source : Source)
  | rejectedTarget | auditMismatch | sharingConflict
  deriving DecidableEq, Repr

structure Memo (native : Native.Profile algorithm Key Source) (lookup : Lookup Key Source) where
  done : (kind : Kind) → (source : Source) → Option (Plan native lookup (.local (kind := kind)) source)
  completed : List (Address Source)

def Memo.empty (native : Native.Profile algorithm Key Source) (lookup : Lookup Key Source) : Memo native lookup :=
  ⟨fun _ _ => none, []⟩

def Memo.insert [DecidableEq Source] {native : Native.Profile algorithm Key Source} {lookup : Lookup Key Source}
    (memo : Memo native lookup) {kind : Kind} {source : Source} (plan : Plan native lookup (.local (kind := kind)) source) :
    Memo native lookup :=
  ⟨fun tag name => if sameKind : tag = kind then
      if sameName : name = source then some (cast (by rw [sameKind, sameName]) plan) else memo.done tag name
    else memo.done tag name, (kind, source) :: memo.completed⟩

def scan {Index : Type} [DecidableEq Index] {Value : Index → Type} {m : Type → Type} [Monad m] :
    (items : List Index) → ((index : Index) → index ∈ items → m (Value index)) →
    m ((index : Index) → index ∈ items → Value index)
  | [], _ => pure (fun _ hit => (List.not_mem_nil hit).elim)
  | first :: rest, visit => do
    let head ← visit first (by simp)
    let tail ← scan rest (fun index hit => visit index (List.mem_cons_of_mem _ hit))
    pure (fun index hit => if same : index = first then same.symm ▸ head
      else tail index ((List.mem_cons.mp hit).resolve_left same))

abbrev Walk (native : Native.Profile algorithm Key Source) (lookup : Lookup Key Source) :=
  StateT (Memo native lookup) (Except (Error Source))

def visitEdge (profile : Profile algorithm Key Source Target Meta) (lookup : Lookup Key Source)
    (visit : (kind : Kind) → (source : Source) → Walk profile.native lookup
      (Plan profile.native lookup (.local (kind := kind)) source)) :
    (edge : Edge Source) → Walk profile.native lookup (Plan profile.native lookup edge.role edge.source)
  | ⟨kind, source, .local⟩ => visit kind source
  | ⟨.commit, source, .gitlink⟩ =>
    if (profile.frontier .commit source).isSome then pure (.external source)
    else throw (.externalGitlink source)

/-- Fuel bounds the depth of uncached local expansion. Active-path repeats are
cycles; completed nodes are reused without spending fuel or re-reading a binding. -/
def walk [LinearOrder Key] [DecidableEq Source] (profile : Profile algorithm Key Source Target Meta)
    (lookup : Lookup Key Source) (fuel : Nat) (active : List (Address Source)) (kind : Kind) (source : Source) :
    Walk profile.native lookup (Plan profile.native lookup (.local (kind := kind)) source) := do
  if (kind, source) ∈ active then throw (.cycle (kind, source))
  else if let some plan := (← get).done kind source then pure plan
  else match fuel with
  | 0 => throw (.fuel (kind, source))
  | remaining + 1 =>
    match found : lookup kind source with
    | .missing => throw (.missing (kind, source))
    | .invalid => throw (.invalid (kind, source))
    | .found binding =>
      if valid : binding.valid profile.native source then do
        let visit := walk profile lookup remaining ((kind, source) :: active)
        let children ← scan binding.node.indices (fun index _ => visitEdge profile lookup visit (binding.node.edge index))
        let plan := Plan.found source binding found valid (fun index => children index (binding.node.mem_indices index))
        modify fun memo => memo.insert plan
        pure plan
      else throw (.invalid (kind, source))
termination_by structural fuel

def discover [LinearOrder Key] [DecidableEq Source] (profile : Profile algorithm Key Source Target Meta)
    (lookup : Lookup Key Source) (fuel : Nat) (kind : Kind) (source : Source) :
    Except (Error Source) (Plan profile.native lookup (.local (kind := kind)) source × Memo profile.native lookup) :=
  (walk profile lookup fuel [] kind source).run (Memo.empty profile.native lookup)

def LocalEdge (lookup : Lookup Key Source) (start finish : Address Source) : Prop :=
  ∃ (binding : Binding Key Source start.1) (index : binding.node.Index),
    lookup start.1 start.2 = .found binding ∧ (binding.node.edge index).role = .local ∧
      ((binding.node.edge index).kind, (binding.node.edge index).source) = finish

inductive Reaches (lookup : Lookup Key Source) (root : Address Source) : Address Source → Prop where
  | here : Reaches lookup root root
  | step {start finish : Address Source} :
      Reaches lookup root start → LocalEdge lookup start finish → Reaches lookup root finish

def nativeNames (native : Native.Profile algorithm Key Source) : Naming.Relation Source ByteArray :=
  fun name bytes => native.assign bytes = name

def externalNames (profile : Profile algorithm Key Source Target Meta) : Correspondence Source Target :=
  fun kind source target => kind = .commit ∧ profile.frontier kind source = some target

def checkedEvent (profile : Profile algorithm Key Source Target Meta) (lookup : Lookup Key Source)
    (event : Event Source Target) : Prop :=
  match event.bytes with
  | some bytes => lookup.observed event.kind event.source bytes ∧ nativeNames profile.native event.source bytes
  | none => externalNames profile event.kind event.source event.target

instance [DecidableEq Source] [DecidableEq Target] (profile : Profile algorithm Key Source Target Meta)
    (lookup : Lookup Key Source) (event : Event Source Target) : Decidable (checkedEvent profile lookup event) := by
  unfold checkedEvent
  split
  · unfold Lookup.observed nativeNames; infer_instance
  · unfold externalNames; infer_instance

def Consistent (events : Finset (Event Source Target)) : Prop :=
  ∀ first ∈ events, ∀ second ∈ events,
    first.kind = second.kind → first.source = second.source → first.target = second.target

instance [DecidableEq Source] [DecidableEq Target] (events : Finset (Event Source Target)) :
    Decidable (Consistent events) := inferInstanceAs (Decidable (∀ first ∈ events, ∀ second ∈ events, _))

/-- Executable checks certify original source bytes, requested root, name sharing,
and permitted external cuts. The wire obligation is separate: the generic DASL
layout API exposes auxiliary blocks as a relation, not an enumerable store. -/
structure Outcome [DecidableEq Key] [DecidableEq Source] [DecidableEq Target]
    (profile : Profile algorithm Key Source Target Meta) (lookup : Lookup Key Source) (kind : Kind) (source : Source) where
  plan : Plan profile.native lookup (.local (kind := kind)) source
  completionOrder : List (Address Source)
  result : Result Source Target
  translated : translate profile plan.expand = some result
  exactName : result.source = source
  checked : ∀ event ∈ result.trace.events.toFinset, checkedEvent profile lookup event
  consistent : Consistent result.trace.events.toFinset

def run [LinearOrder Key] [DecidableEq Source] [DecidableEq Target] (profile : Profile algorithm Key Source Target Meta)
    (lookup : Lookup Key Source) (fuel : Nat) (kind : Kind) (source : Source) :
    Except (Error Source) (Outcome profile lookup kind source) := do
  let (plan, memo) ← discover profile lookup fuel kind source
  match translated : translate profile plan.expand with
  | none => throw .rejectedTarget
  | some result =>
    if named : result.source = source then
      let events := result.trace.events.toFinset
      if checked : ∀ event ∈ events, checkedEvent profile lookup event then
        if consistent : Consistent events then
          pure ⟨plan, memo.completed.reverse, result, translated, named, checked, consistent⟩
        else throw .sharingConflict
      else throw .auditMismatch
    else throw .auditMismatch

end Silmaril.Formats.Git.Translate.Graph
