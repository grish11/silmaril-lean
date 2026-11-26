module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Thms
public import Silmaril.Languages.Starlark.Modules.Resolve.Thms
public import Silmaril.Languages.Starlark.Functions.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry

open Silmaril.Languages.Starlark (Binding Scope)
open Silmaril.Languages.Starlark.Lists (State Slot Cell Address Value Outcome)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Modules (enter globalSlot fileSlot validateSource)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry

private theorem added_cell (state : State) (binding : Binding) :
    (state.allocateSlot binding).slots binding = some (.owned state.heap.size) ∧
    (state.allocateSlot binding).heap[state.heap.size]? = some ⟨.binding none, false⟩ := by
  simp [State.allocateSlot]

private theorem push_preserves_cell (state : State) {address : Address} {cell : Cell}
    (present : state.heap[address]? = some cell) (extra : Cell) :
    (state.heap.push extra)[address]? = some cell := by
  have within := (Array.getElem?_eq_some_iff.mp present).choose
  simp [Array.getElem?_push, Nat.ne_of_lt within, present]

private theorem allocate_owned_cells (initial : State) (binding : Binding) (valid : OwnedCells initial) :
    OwnedCells (initial.allocateSlot binding) := by
  intro name address found
  by_cases same : name = binding
  · subst name
    have equal := (added_cell initial binding).1.symm.trans found
    cases equal
    exact ⟨none, false, (added_cell initial binding).2⟩
  · have old : initial.slots name = some (.owned address) := by
      simpa [State.allocateSlot, same] using found
    obtain ⟨value, frozen, present⟩ := valid name address old
    exact ⟨value, frozen, push_preserves_cell _ present _⟩

private theorem allocate_all_owned (names : List Binding) (initial : State) (valid : OwnedCells initial) :
    OwnedCells (names.foldl State.allocateSlot initial) := by
  induction names generalizing initial with
  | nil => exact valid
  | cons first rest ih => exact ih _ (allocate_owned_cells _ first valid)

theorem allocate_blank (names : List Binding) (initial : State) (binding : Binding)
    (requested : binding ∈ names ∨ ∃ address, initial.slots binding = some (.owned address) ∧
      initial.heap[address]? = some ⟨.binding none, false⟩) :
    let result := names.foldl State.allocateSlot initial
    ∃ address, result.slots binding = some (.owned address) ∧
      result.heap[address]? = some ⟨.binding none, false⟩ := by
  induction names generalizing initial with
  | nil => exact requested.resolve_left (by simp)
  | cons first rest ih =>
    by_cases same : binding = first
    · subst first
      exact ih _ (.inr ⟨_, added_cell initial binding⟩)
    · apply ih _
      rcases requested with inList | ⟨address, slot, cell⟩
      · exact .inl ((List.mem_cons.mp inList).resolve_left same)
      · exact .inr ⟨address, by simp [State.allocateSlot, same, slot], push_preserves_cell _ cell _⟩

private theorem write_owned_cells (state : State) (name : Binding) (value : Value) (valid : OwnedCells state) :
    OwnedCells (state.write name value) := by
  intro binding address found
  have old : state.slots binding = some (.owned address) := by
    unfold State.write at found
    split at found <;> try exact found
    split at found <;> exact found
  unfold State.write
  split
  · exact valid binding address old
  · exact valid binding address old
  · split
    · rename_i ownerAddress _ _ contents frozen cell
      by_cases same : ownerAddress = address
      · subst address
        have within := (Array.getElem?_eq_some_iff.mp cell).choose
        exact ⟨some value, frozen, by simp [within]⟩
      · obtain ⟨before, oldFrozen, oldCell⟩ := valid binding address old
        exact ⟨before, oldFrozen, by simp [same, oldCell]⟩
    · exact valid binding address old

theorem activate_owned_cells (state : State) (declaration : Declaration) (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (arguments : List (Binding × Value)) : OwnedCells (activate state declaration captures arguments) := by
  have writes (assigned : List (Binding × Value)) (state : State) (valid : OwnedCells state) :
      OwnedCells (assigned.foldl (fun s (binding, value) => s.write binding value) state) := by
    induction assigned generalizing state with
    | nil => exact valid
    | cons first rest ih => exact ih _ (write_owned_cells _ _ _ valid)
  apply writes
  apply allocate_all_owned
  intro binding address found
  change capturedSlots captures binding = some (.owned address) at found
  cases hit : captures.find? (fun capture => capture.binding == binding) <;>
    simp [capturedSlots, hit] at found

theorem activated_cell (state : State) (frame : Frame) (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (arguments : List (Binding × Value)) (name : String) (declared : name ∈ frame.owned) :
    let active := activate state frame.declaration captures arguments
    ∃ address value frozen, active.slots (fileSlot name) = some (.owned address) ∧
      active.heap[address]? = some ⟨.binding value, frozen⟩ := by
  have member : fileSlot name ∈ frame.declaration.signature.slots ++ frame.declaration.locals := by
    simp [Frame.declaration, Frame.owned, requiredSignature, Signature.slots, Signature.named] at declared ⊢
    exact declared.elim (fun h => .inl ⟨_, h, rfl⟩) (fun h => .inr ⟨_, h, rfl⟩)
  obtain ⟨address, slot⟩ := activate_owned state frame.declaration captures arguments (fileSlot name) member
  obtain ⟨value, frozen, cell⟩ := activate_owned_cells state frame.declaration captures arguments _ _ slot
  exact ⟨address, value, frozen, slot, cell⟩

theorem checked_module_globals {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved) :
    resolved.source.globals = globals :=
  (checked_of_resolve checked).2.1.trans
    (congrArg (fun block : BlockContext => block.reads.globals) (moduleBlock_eq declares))

theorem checked_global_cell {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (caller : State) (name : String) (global : name ∈ globals) :
    ∃ address, (enter resolved.source caller).slots (globalSlot name) = some (.owned address) ∧
      (enter resolved.source caller).heap[address]? = some ⟨.binding none, false⟩ := by
  have declared : name ∈ resolved.source.globals := checked_module_globals declares checked ▸ global
  exact allocate_blank _ _ _
    (.inl (List.mem_append_left _ (List.mem_map.mpr ⟨name, declared, rfl⟩)))

theorem checked_global_read {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (caller : State) (name : String) (global : name ∈ globals) :
    (enter resolved.source caller).bindingValue (globalSlot name) = .error (.uninitialized (globalSlot name)) := by
  obtain ⟨address, slot, cell⟩ := checked_global_cell declares checked caller name global
  simp only [State.bindingValue, slot, Slot.address, cell]

private theorem first_duplicate_none (names : List String) : firstDuplicate names = none ↔ names.Nodup := by
  induction names with
  | nil => simp [firstDuplicate]
  | cons first rest ih =>
    by_cases member : first ∈ rest <;> simp [firstDuplicate, member, ih]

private theorem required_slots (names : List String) : (requiredSignature names).slots = names.map fileSlot := by
  simp [requiredSignature, Signature.slots, Signature.named, Function.comp_def]

theorem required_nodup (names : List String) (checked : (requiredSignature names).validate = .ok ()) :
    names.Nodup := by
  have slots : (requiredSignature names).slots.map Binding.name = names := by
    simp [required_slots, Function.comp_def, fileSlot]
  apply (first_duplicate_none names).mp
  unfold Signature.validate at checked
  rw [slots] at checked
  cases found : firstDuplicate names with
  | none => rfl
  | some duplicate => simp [found] at checked; contradiction

private theorem mapped_nodup (names : List String) (unique : names.Nodup) : (names.map fileSlot).Nodup := by
  induction names with
  | nil => simp
  | cons first rest ih =>
    have head := (List.nodup_cons.mp unique).1
    have tail := (List.nodup_cons.mp unique).2
    simp [ih tail, List.mem_map, fileSlot, head]

private theorem filled_positional (slots : List Binding) (values : List Value) (unique : slots.Nodup) :
    (slots.map fun slot => (slot, List.lookup slot (slots.zip values))) =
      (slots.zip values).map (fun (slot, value) => (slot, some value)) ++
        (slots.drop values.length).map (fun slot => (slot, none)) := by
  induction slots generalizing values with
  | nil => simp
  | cons first rest ih =>
    cases values with
    | nil => simp
    | cons value values =>
      have absent := (List.nodup_cons.mp unique).1
      have tail := (List.nodup_cons.mp unique).2
      have hides :
          (rest.map fun slot => (slot, List.lookup slot ((first, value) :: rest.zip values))) =
            rest.map fun slot => (slot, List.lookup slot (rest.zip values)) := by
        apply List.map_congr_left
        intro slot present
        have different : slot ≠ first := fun equal => absent (equal ▸ present)
        have unequal : (slot == first) = false := by simp [different]
        simp [List.lookup, unequal]
      simp only [List.zip_cons_cons, List.map_cons, List.cons_append, List.length_cons, List.drop_succ_cons]
      rw [hides, ih values tail]
      simp [List.lookup]

private theorem required_binding_result (names : List String) (values : List Value) (unique : names.Nodup) :
    bindArguments (requiredSignature names) [] ⟨values, []⟩ =
      if names.length < values.length then .error (.arity names.length values.length)
      else if values.length < names.length then .error (.missingArguments (names.drop values.length))
      else .ok ⟨(names.map fileSlot).zip values, [], []⟩ := by
  let slots := names.map fileSlot
  let paired := slots.zip values
  let filled := slots.map fun slot => (slot, List.lookup slot paired)
  have fillEq : filled = paired.map (fun (slot, value) => (slot, some value)) ++
      (slots.drop values.length).map (fun slot => (slot, none)) :=
    filled_positional slots values (mapped_nodup names unique)
  have unfilled : slots.drop values.length = (names.drop values.length).map fileSlot := by
    simp [slots]
  have missing : (filled.filterMap fun (slot, value) => if value.isNone then some slot.name else none) =
      names.drop values.length := by
    rw [fillEq, unfilled]
    simp [List.filterMap_append, List.filterMap_map, -List.map_drop, Function.comp_def, fileSlot]
  have supplied : (filled.filterMap fun (slot, v) => v.map fun value => (slot, value)) = paired := by
    rw [fillEq, unfilled]
    simp [List.filterMap_append, List.filterMap_map, -List.map_drop]
  have positional : (requiredSignature names).positional.map Parameter.slot = slots := by
    simp [requiredSignature, slots, Function.comp_def]
  by_cases surplus : names.length < values.length
  · have extra : ¬ (values.drop names.length).isEmpty = true := by
      simpa [List.drop_eq_nil_iff] using (by omega : ¬ values.length ≤ names.length)
    simp [bindArguments, surplus, extra, requiredSignature]; rfl
  · have noExtra : values.drop slots.length = [] :=
      List.drop_eq_nil_iff.mpr (by simp [slots]; omega)
    let computed := (requiredSignature names).named.map fun p =>
      (p.slot, (List.lookup p.slot paired).orElse fun () => List.lookup p.slot [])
    have fillArgs : computed = filled := by
      simp [computed, requiredSignature, Signature.named, Function.comp_def, slots, filled]
    have fillBind : bindArguments (requiredSignature names) [] ⟨values, []⟩ =
        (do
          if !(filled.filterMap fun (slot, value) => if value.isNone then some slot.name else none).isEmpty then
            throw (.missingArguments (filled.filterMap fun (slot, value) =>
              if value.isNone then some slot.name else none))
          return ⟨filled.filterMap (fun (slot, v) => v.map fun value => (slot, value)), [], []⟩) := by
      simp only [bindArguments, positional, noExtra, List.isEmpty_nil, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, ite_false, List.foldlM_nil]
      change (show Except Silmaril.Languages.Starlark.Lists.Error BoundArguments from do
        if !(computed.filterMap fun pair => if pair.2.isNone then some pair.1.name else none).isEmpty then
          throw (.missingArguments (computed.filterMap fun pair =>
            if pair.2.isNone then some pair.1.name else none))
        return ⟨computed.filterMap (fun pair => pair.2.map fun value => (pair.1, value)), [], []⟩) = _
      rw [fillArgs]
    rw [fillBind, missing, supplied]
    by_cases short : values.length < names.length
    · have nonempty : ¬ (names.drop values.length).isEmpty = true := by
        simpa [List.drop_eq_nil_iff] using (by omega : ¬ names.length ≤ values.length)
      simp [short, nonempty, surplus]; rfl
    · have empty : names.drop values.length = [] := List.drop_eq_nil_iff.mpr (by omega)
      simp [short, surplus, empty, paired, slots]; rfl

private theorem assigned_layout {names : List String} {values : List Value} {assigned : List (Binding × Value)}
    (evidence : Assigns names values assigned) :
    names.length = values.length ∧ (names.map fileSlot).zip values = assigned := by
  induction evidence with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ ih => simp [ih.1, ih.2]

theorem binds_total (names : List String) (values : List Value) : ∃ result, Binds names values result := by
  have exactArity : ∀ (names : List String) (values : List Value), names.length = values.length →
      Assigns names values ((names.map fileSlot).zip values) := by
    intro names
    induction names with
    | nil =>
      intro values equal
      cases values with
      | nil => exact .nil
      | cons => simp at equal
    | cons name names ih =>
      intro values equal
      cases values with
      | nil => simp at equal
      | cons value values => exact .cons (ih values (Nat.succ.inj equal))
  by_cases short : values.length < names.length
  · exact ⟨_, .missing short⟩
  by_cases long : names.length < values.length
  · exact ⟨_, .surplus long⟩
  exact ⟨_, .success (exactArity names values (by omega))⟩

theorem required_binds {names : List String} {values : List Value}
    {result : Except Silmaril.Languages.Starlark.Lists.Error (List (Binding × Value))}
    (checked : (requiredSignature names).validate = .ok ()) (binds : Binds names values result) :
    bindArguments (requiredSignature names) [] ⟨values, []⟩ =
      result.map (fun assigned => ⟨assigned, [], []⟩) := by
  rw [required_binding_result names values (required_nodup names checked)]
  cases binds with
  | success assigned =>
    have ⟨lengths, zip⟩ := assigned_layout assigned
    simp [lengths, zip, Except.map]
  | missing short => simp [short, (show ¬ names.length < values.length by omega), Except.map]
  | surplus long => simp [long, Except.map]

theorem prepare_required (program : Program) (available : List DeclarationId) (frame : Frame)
    (id : DeclarationId) (permitted : id ∈ available) (state : State) (address : Address)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture) (frozen : Bool) (values : List Value)
    (result : Except Silmaril.Languages.Starlark.Lists.Error (List (Binding × Value)))
    (stored : state.heap[address]? = some ⟨.function ⟨id, captures, []⟩, frozen⟩)
    (found : program[id]? = some frame.declaration)
    (checked : frame.declaration.signature.validate = .ok ()) (binds : Binds frame.parameters values result) :
    prepareExpanded program available ⟨values, []⟩ (.function address) state =
      match result with
      | .ok assigned => .ok (.closure ⟨id, permitted, frame.code⟩) (activate state frame.declaration captures assigned)
      | .error error => .error error state := by
  have binding : bindArguments frame.declaration.signature [] ⟨values, []⟩ =
      result.map (fun assigned => ⟨assigned, [], []⟩) := required_binds checked binds
  have loaded : getClosure address state = .ok ⟨id, captures, []⟩ state := by
    simp [getClosure, Silmaril.Languages.Starlark.Lists.projectCell, Silmaril.Languages.Starlark.Lists.getCell,
      bind, EStateM.bind, stored]
    rfl
  cases result <;>
    simp only [prepareExpanded, bind, EStateM.bind, loaded, found, permitted, dite_true,
      binding, Except.map, Silmaril.Languages.Starlark.Lists.fromExcept] <;> rfl

private theorem good_signatures (program : Program) (body : Body) (checked : validate program body = .ok ())
    (declaration : Declaration) (index : Nat) (found : program[index]? = some declaration) :
    declaration.signature.validate = .ok () := by
  unfold validate at checked
  rw [← Array.forIn_toList] at checked
  let check (entry : Declaration) (_ : Unit) : Except CallStaticError (ForInStep Unit) := do
    entry.validate
    return .yield ()
  change ((forIn program.toList () check) >>= fun _ => body.validateCalls) = .ok () at checked
  have all : forIn program.toList () check = .ok () := by
    cases ran : forIn program.toList () check with
    | ok result => cases result; rfl
    | error => rw [ran] at checked; cases checked
  have member : declaration ∈ program.toList := Array.mem_toList_iff.mpr
    (Array.mem_iff_getElem?.mpr ⟨index, found⟩)
  generalize program.toList = entries at all member
  induction entries with
  | nil => cases member
  | cons first rest ih =>
    rw [List.forIn_cons] at all
    cases valid : first.validate with
    | error error =>
      have rejected : check first () = .error error := by unfold check; rw [valid]; rfl
      rw [rejected] at all
      cases all
    | ok result =>
      cases result
      have accepted : check first () = .ok (.yield ()) := by unfold check; rw [valid]; rfl
      rw [accepted] at all
      rcases List.mem_cons.mp member with rfl | tail
      · unfold Declaration.validate at valid
        cases signature : declaration.signature.validate with
        | ok result => cases result; rfl
        | error => rw [signature] at valid; cases valid
      · exact ih all tail

theorem checked_signature {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (declaration : Declaration) (index : Nat)
    (found : resolved.program[index]? = some declaration) : declaration.signature.validate = .ok () := by
  have compiled := (checked_of_resolve checked).2.2.2
  unfold validateSource at compiled
  split at compiled
  · cases compiled
  · generalize validEq : validate resolved.program (.total (.atomic .pass)) = valid at compiled
    cases valid with
    | error => cases compiled
    | ok result => cases result; exact good_signatures _ _ validEq _ _ found

theorem checked_prepare {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (available : List DeclarationId) (frame : Frame)
    (id : DeclarationId) (permitted : id ∈ available) (state : State) (address : Address)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture) (frozen : Bool) (values : List Value)
    (result : Except Silmaril.Languages.Starlark.Lists.Error (List (Binding × Value)))
    (stored : state.heap[address]? = some ⟨.function ⟨id, captures, []⟩, frozen⟩)
    (found : resolved.program[id]? = some frame.declaration) (binds : Binds frame.parameters values result) :
    prepareExpanded resolved.program available ⟨values, []⟩ (.function address) state =
      match result with
      | .ok assigned => .ok (.closure ⟨id, permitted, frame.code⟩) (activate state frame.declaration captures assigned)
      | .error error => .error error state :=
  prepare_required resolved.program available frame id permitted state address captures frozen values result
    stored found (checked_signature checked _ _ found) binds

private theorem root_declared {commands : List Command} {globals : List String}
    (declares : ModuleBinders commands globals) (chain : Chain)
    (member : Command.define chain.name (.required chain.parameters) chain.body ∈ commands) :
    chain.name ∈ globals := by
  induction declares with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · cases first
      exact List.mem_append_left _ List.mem_cons_self
    · exact List.mem_append_right _ (ih tail)

theorem checked_root_installs {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule} {chain : Chain} {head : Frame} {rest : List Frame}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (emitted : Emits globals [] chain (head :: rest)) (caller : State) :
    ∃ captures, Installs (enter resolved.source caller) head.free captures := by
  apply installs_of_addresses
  intro entry present
  obtain ⟨name, member, same⟩ := root_capture emitted entry present
  obtain ⟨address, slot, _⟩ := checked_global_cell declares checked caller name member
  exact ⟨globalSlot name, address, same, .inl slot⟩

theorem checked_root_definition {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule} {chain : Chain} {head : Frame} {rest : List Frame}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (emitted : Emits globals [] chain (head :: rest))
    (site : Command.define chain.name (.required chain.parameters) chain.body ∈ commands)
    (caller : State) (id : Nat) (found : resolved.program[id]? = some head.declaration) :
    let initial := enter resolved.source caller
    ∃ next captures, Installs initial head.free captures ∧
      run resolved.program (.define (globalSlot chain.name) id) initial = .ok .next next ∧
      next.bindingValue (globalSlot chain.name) = .ok (.function initial.heap.size) ∧
      next.heap[initial.heap.size]? = some ⟨.function ⟨id, captures, []⟩, false⟩ := by
  let initial := enter resolved.source caller
  obtain ⟨captures, installed⟩ := checked_root_installs declares checked emitted caller
  obtain ⟨address, slot, cell⟩ := checked_global_cell declares checked caller chain.name
    (root_declared declares chain site)
  obtain ⟨next, corresponds, binding, stored⟩ := define_installs resolved.program head.declaration id
    (globalSlot chain.name) initial caller address none false captures found installed slot cell
  refine ⟨next, captures, installed, ?_, binding, stored⟩
  have defaults : defaultOperands resolved.program id = [] := by
    simp [defaultOperands, found, Frame.declaration, requiredSignature, Signature.defaulted, Signature.named,
      List.filterMap_map]
  rw [run, denoteBody]
  simpa [defaults, pure, EStateM.pure, Outcome.resume] using corresponds

theorem checked_root_dispatch {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule} {chain : Chain} {head : Frame} {rest : List Frame}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (emitted : Emits globals [] chain (head :: rest))
    (site : Command.define chain.name (.required chain.parameters) chain.body ∈ commands)
    (caller : State) (id : Nat) (found : resolved.program[id]? = some head.declaration)
    {values : List Value} {result : Except Silmaril.Languages.Starlark.Lists.Error (List (Binding × Value))}
    (binds : Binds head.parameters values result) :
    let initial := enter resolved.source caller
    let available := List.range resolved.program.size
    ∃ next captures, ∃ permitted : id ∈ available,
      Installs initial head.free captures ∧
      Exec resolved.program available initial (.define (globalSlot chain.name) id) (.ok .next next) ∧
      next.bindingValue (globalSlot chain.name) = .ok (.function initial.heap.size) ∧
      prepareExpanded resolved.program available ⟨values, []⟩ (.function initial.heap.size) next =
        match result with
        | .ok assigned =>
          .ok (.closure ⟨id, permitted, head.code⟩) (activate next head.declaration captures assigned)
        | .error error => .error error next := by
  obtain ⟨next, captures, installed, ran, binding, stored⟩ :=
    checked_root_definition declares checked emitted site caller id found
  have permitted : id ∈ List.range resolved.program.size :=
    List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
  exact ⟨next, captures, permitted, installed, (exec_iff_denoteBody _ _ _ _ _).mpr ran, binding,
    checked_prepare checked _ head id permitted next _ captures false values result stored found binds⟩

theorem checked_entry_read_error {commands : List Command} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved)
    (caller : State) (name : String) (global : name ∈ globals) :
    let initial := enter resolved.source caller
    run resolved.program (.evalExpr (.atom (.read (.bound (globalSlot name))))) initial =
      .error (.uninitialized (globalSlot name)) initial := by
  let initial := enter resolved.source caller
  have error : initial.read (.bound (globalSlot name)) =
      .error (.uninitialized (globalSlot name)) initial := by
    simp [initial, State.read, checked_global_read declares checked caller name global]
  have reads : Silmaril.Languages.Starlark.Lists.Eval initial (.read (.bound (globalSlot name)))
      (.error (.uninitialized (globalSlot name)) initial) :=
    error ▸ Silmaril.Languages.Starlark.Lists.Eval.read
  apply (exec_iff_denoteBody _ _ _ _ _).mp
  exact .evalExpr (.evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
    (.atom trivial reads))

theorem checked_first_read_error {rest : List Command} {globals : List String} {name : String}
    {linked : Program} {resolved : ResolvedModule}
    (declares : ModuleBinders (.eval (.scalar (.read name)) :: rest) globals)
    (checked : resolve (.eval (.scalar (.read name)) :: rest) linked = .ok resolved)
    (legal : name.toList.head? ≠ some '$') (global : name ∈ globals)
    (host : Silmaril.Languages.Starlark.Modules.Catalog) (caller : State) :
    let initial := enter resolved.source caller
    runModule (.eval (.scalar (.read name)) :: rest) host caller linked =
      .ok (.error (.runtime (.uninitialized (globalSlot name)))
        (Silmaril.Languages.Starlark.Modules.restoreThread caller initial)) := by
  open Silmaril.Languages.Starlark.Functions.Lowering.Resolve in
  have operand : resolveTracked (moduleBlock (.eval (.scalar (.read name)) :: rest)).reads
      (.scalar (.read name)) = .ok (.atom (.read (.bound (globalSlot name))), [globalSlot name]) := by
    simp [moduleBlock_eq declares, Assignment.LexicalBlock.context, resolveTracked, resolveExpr,
      resolveScalar, resolveRead, resolveReadValue, Silmaril.Languages.Starlark.resolveName,
      legal, global, globalSlot, Except.map]
  have ⟨elaborated, _, _, valid⟩ := checked_of_resolve checked
  obtain ⟨suffix, commands⟩ := elaborateCommands_eval_cons _ rest linked _ _ operand _ _ elaborated
  simp [runModule, checked, Silmaril.Languages.Starlark.Modules.initializeModule, valid, commands,
    Silmaril.Languages.Starlark.Modules.runCommands, Silmaril.Languages.Starlark.Modules.runCommand,
    Silmaril.Languages.Starlark.Modules.TopCode.body, checked_entry_read_error declares checked caller name global,
    Silmaril.Languages.Starlark.Modules.afterCode, Silmaril.Languages.Starlark.Modules.finish]

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Entry
