module

public import Silmaril.Semantics.Arena.Defs

@[expose] public section

namespace Silmaril.Semantics.Arena.Mutable

variable {Rep Key Obj Error Result Next Name : Type}

/-- `none` is a hole, `some none` is an occupied reservation. -/
abbrev Cell (Obj : Type) := Option (Option Obj)

/-- Only a successful edit returns a successor. This is a pure specification
of exclusive state passing, not a Lean linearity or Rust borrow-checking claim. -/
abbrev Mutation (Rep Error Result : Type) := Rep → Except Error (Result × Rep)

namespace Mutation

def bind (first : Mutation Rep Error Result) (next : Result → Mutation Rep Error Next) :
    Mutation Rep Error Next := fun state =>
  (first state).bind fun (result, successor) => next result successor

/-- Observe the commit result and the state that remains visible. An error
publishes neither the final edit nor any intermediate edit in a composition. -/
def commit (edit : Mutation Rep Error Result) (state : Rep) : Except Error Result × Rep :=
  match edit state with
  | .ok (result, successor) => (.ok result, successor)
  | .error fault => (.error fault, state)

end Mutation

/-- Insert requires a hole. Replace (including filling a reservation) and remove
require occupancy. A plain replace explicitly drops any attached name. -/
inductive Change (Obj : Type) where
  | reserve
  | insert (obj : Obj)
  | replace (obj : Obj)
  | remove

namespace Change

def apply (change : Change Obj) (cell : Option (Slot Name Obj)) : Except Fault (Option (Slot Name Obj)) :=
  match change with
  | .reserve => (Edit.reserve none).apply cell
  | .insert obj => ((Edit.reserve none).apply cell).map fun _ => some ⟨none, some obj⟩
  | .replace obj => (Edit.replace ⟨none, some obj⟩).apply cell
  | .remove => Edit.clear.apply cell

def run (change : Change Obj) (step : Rep → Key → Edit Name Obj → Except Fault Rep)
    (key : Key) (state : Rep) : Except Fault Rep :=
  match change with
  | .reserve => step state key (.reserve none)
  | .insert obj => (step state key (.reserve none)).bind fun reserved =>
      step reserved key (.replace ⟨none, some obj⟩)
  | .replace obj => step state key (.replace ⟨none, some obj⟩)
  | .remove => step state key .clear

end Change

/-- Minimal read and explicit-key mutation capability. A backend with a vacant
key selector or append need not expose allocation through this interface. -/
structure Access (Rep Key Obj Error : Type) where
  read : Rep → Key → Cell Obj
  change : Key → Change Obj → Mutation Rep Error Unit

namespace Access

def ofSlots (read : Rep → Key → Option (Slot Name Obj))
    (step : Rep → Key → Edit Name Obj → Except Fault Rep) : Access Rep Key Obj Fault where
  read state key := (read state key).map Slot.payload
  change key operation state := (operation.run step key state).map ((), ·)

def raw [DecidableEq Key] : Access (State Key Name Obj) Key Obj Fault := ofSlots (fun state => state) State.step

def array (limit : Nat) : Access (Dense limit Name Obj) Nat Obj Fault := ofSlots Dense.read Dense.step

end Access

/-- Optional fresh-key capability. `none` reserves without a payload. `Empty`
can be used for the error type of a total model allocator. -/
abbrev Allocator (Rep Key Obj Error : Type) := Option Obj → Mutation Rep Error Key

abbrev Growing (Name Obj : Type) := (limit : Nat) × Dense limit Name Obj

namespace Growing

def read (state : Growing Name Obj) (key : Nat) : Cell Obj := (state.2.read key).map Slot.payload

def allocate : Allocator (Growing Name Obj) Nat Obj Empty := fun payload state =>
  .ok (state.1, ⟨state.1 + 1, state.2.append ⟨none, payload⟩⟩)

end Growing

end Silmaril.Semantics.Arena.Mutable
