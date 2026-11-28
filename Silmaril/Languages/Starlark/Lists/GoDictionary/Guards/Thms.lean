module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Guards.Defs
public import Silmaril.Languages.Starlark.Lists.Iteration.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards.Physical
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards.Agreement
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Guards.Denotation

public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Guards

/-- An open mutation has neither a freeze flag nor an active iterator. -/
theorem allowed_iff (table : Table) :
    table.rejection = none ↔ table.frozen = false ∧ table.activeIterators = 0 :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.allowed_iff table

/-- Set and direct delete reject before any key operation and preserve the entire table. -/
theorem rejects (heap : Heap) (table : Table) (key value : Value) (reason : Rejection)
    (blocked : table.rejection = some reason) :
    Guards.set heap table key value = .error (.guard reason) table ∧
    delete heap table key = .error (.guard reason) table :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.rejects heap table key value reason blocked

/-- A successful set installs the new initialized contents. -/
theorem set_ready (heap : Heap) (table : Table) (key value : Value) (next : Deletion.Table)
    (allowed : table.rejection = none)
    (ran : Lists.GoDictionary.Deletion.set heap table.rows key value = .ok next) :
    Guards.set heap table key value = .ok () { table with contents := some next } :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.set_ready heap table key value next allowed ran

/-- Initializing already allocated storage preserves the table. -/
theorem initialize_allocated (table : Table) (rows : Deletion.Table)
    (allocated : table.contents = some rows) : table.initialize = table :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.initialize_allocated table rows allocated

/-- A reached hash error retains the allocated table and every original row. -/
theorem set_hash_error (heap : Heap) (table : Table) (key value : Value) (error : Error)
    (allowed : table.rejection = none) (hashed : hashKey heap key = .error error) :
    Guards.set heap table key value = .error (.table error) table.initialize :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.set_hash_error heap table key value error allowed hashed

/-- Direct delete misses before hashing on a mutable unallocated table. -/
theorem delete_unallocated (heap : Heap) (table : Table) (key : Value)
    (allowed : table.rejection = none) (empty : table.contents = none) :
    delete heap table key = .ok none table :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.delete_unallocated heap table key allowed empty

/-- Direct delete on allocated storage propagates the reached hash error. -/
theorem delete_hash_error (heap : Heap) (table : Table) (key : Value)
    (rows : Deletion.Table) (error : Error) (allowed : table.rejection = none)
    (allocated : table.contents = some rows) (hashed : hashKey heap key = .error error) :
    delete heap table key = .error (.table error) table :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.delete_hash_error heap table key rows error allowed allocated hashed

/-- An admitted direct delete retains the underlying removed value and exact state. -/
theorem delete_ready (heap : Heap) (table : Table) (key : Value)
    (rows next : Deletion.Table) (removed : Option Value)
    (allowed : table.rejection = none) (allocated : table.contents = some rows)
    (ran : Lists.GoDictionary.Deletion.delete heap rows key = .ok (removed, next)) :
    delete heap table key = .ok removed { table with contents := some next } :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.delete_ready heap table key rows next removed allowed allocated ran

/-- The unallocated Go table relates to a live empty canonical dictionary. -/
theorem zero_related (state : State) (address : Lists.Address) (table : Table)
    (cell : state.heap[address]? = some ⟨.dict [], table.frozen⟩)
    (active : table.frozen = false → (0 < table.activeIterators ↔ address ∈ state.iterators)) (zero : table.contents = none) :
    Related state address table [] :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.zero_related state address table cell active zero

/-- Entering an iterator preserves the relation, including the frozen Go count policy. -/
theorem enterIterator_related (state : State) (address : Lists.Address) (table : Table)
    (entries : List Entry) (related : Related state address table entries) :
    Related (Lists.Iteration.pushIterator state address) address table.enterIterator entries :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.enterIterator_related state address table entries related

/-- All keys observe the same guard priority in the two assignment paths. -/
theorem guard_agrees (state : State) (address : Lists.Address) (table : Table) (entries : List Entry)
    (key value : Value) (reason : Rejection)
    (related : Related state address table entries) (blocked : table.rejection = some reason) :
    Guards.set state.heap table key value = .error (.guard reason) table ∧
      delete state.heap table key = .error (.guard reason) table ∧
      writeDict address key value state = .error (reason.canonicalError address) state :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.guard_agrees state address table entries key value reason related blocked

/-- Canonical receiver lookup rejects a missing cell before the guards or key validation. -/
theorem writeDict_dangling (state : State) (address : Lists.Address) (key value : Value)
    (missing : state.heap[address]? = none) :
    writeDict address key value state = .error (.danglingAddress address) state :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.writeDict_dangling state address key value missing

/-- A shared unhashable key preserves live rows with the separately stated storage effect. -/
theorem writeDict_unhashable (state : State) (address : Lists.Address) (table : Table)
    (entries : List Entry) (key value : Value)
    (related : Related state address table entries) (allowed : table.rejection = none)
    (shape : Unhashable key) :
    Guards.set state.heap table key value =
        .error (.table (.unsupportedKey key)) table.initialize ∧
      writeDict address key value state = .error (.unhashableKey key) state :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.writeDict_unhashable state address table entries key value related allowed shape

/-- Scalar writes, guard rejection and shared unhashable-key rejection preserve the related observations. -/
theorem writeDict_lockstep (state : State) (address : Lists.Address) (table : Table)
    (entries : List Entry) (key value : Value) (related : Related state address table entries)
    (domain : (∃ scalar, key = .scalar scalar) ∨ Unhashable key) :
    AssignsTogether state address table entries
      (Guards.set state.heap table key value)
      (writeDict address key value state) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.writeDict_lockstep state address table entries key value related domain

/-- Assignment evaluates the right-hand side, receiver and key before invoking the mutation. -/
theorem denote_setIndex (state : State) (receiver index rhs : Expr) :
    denote (.setIndex receiver index rhs) state =
      Lists.Outcome.resume (denote rhs state) (fun value afterRhs =>
        Lists.Outcome.resume (denote receiver afterRhs) (fun target afterReceiver =>
          Lists.Outcome.resume (denote index afterReceiver) (fun key => writeIndex target key value))) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.denote_setIndex state receiver index rhs

/-- An uninitialized receiver reports its binding error at the state reached after the right-hand side. -/
theorem setIndex_uninitialized (state afterRhs : State) (binding : Binding)
    (index rhs : Expr) (value : Value)
    (right : denote rhs state = .ok value afterRhs)
    (missing : afterRhs.bindingValue binding = .error (.uninitialized binding)) :
    denote (.setIndex (.read (.bound binding)) index rhs) state =
      .error (.uninitialized binding) afterRhs :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.setIndex_uninitialized state afterRhs binding index rhs value right missing

/-- A key-expression error precedes the write guard and retains its reached state. -/
theorem setIndex_key_error (state afterRhs afterReceiver afterKey : State)
    (receiver index rhs : Expr) (target value : Value) (error : Lists.Error)
    (right : denote rhs state = .ok value afterRhs)
    (readReceiver : denote receiver afterRhs = .ok target afterReceiver)
    (readKey : denote index afterReceiver = .error error afterKey) :
    denote (.setIndex receiver index rhs) state = .error error afterKey :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.setIndex_key_error state afterRhs afterReceiver afterKey receiver index rhs target value error right readReceiver readKey

/-- Mutation lockstep starts in the state reached after key evaluation. -/
theorem setIndex_lockstep (state afterRhs afterReceiver afterKey : State) (address : Lists.Address)
    (table : Table) (entries : List Entry) (receiver index rhs : Expr) (key value : Value)
    (right : denote rhs state = .ok value afterRhs)
    (readReceiver : denote receiver afterRhs = .ok (.dict address) afterReceiver)
    (readKey : denote index afterReceiver = .ok key afterKey)
    (related : Related afterKey address table entries)
    (domain : (∃ scalar, key = .scalar scalar) ∨ Unhashable key) :
    AssignsTogether afterKey address table entries
      (Guards.set afterKey.heap table key value)
      (denote (.setIndex receiver index rhs) state) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.setIndex_lockstep state afterRhs afterReceiver afterKey address table entries receiver index rhs key value right readReceiver readKey related domain

/-- The display helper validates the key before attempting its cell edit. -/
theorem display_unhashable (state : State) (address : Lists.Address) (entries : List Entry)
    (frozen : Bool) (key value : Value)
    (cell : state.heap[address]? = some ⟨.dict entries, frozen⟩) (shape : Unhashable key) :
    Lists.insertDisplayEntry (.dict address) key value state = .error (.unhashableKey key) state :=
  Proofs.Languages.Starlark.Lists.GoDictionary.Guards.display_unhashable state address entries frozen key value cell shape

end Silmaril.Languages.Starlark.Lists.GoDictionary.Guards
