module

public import Silmaril.Languages.Python.Source.Closure.Thms

/-! # Source frame slots and parameter destinations

Ordinary locals exclude the frame's owned cells. Each parameter destination
names one bounded slot with the analyzed local access and the corresponding
name lookup. A successful layout retains the source parameter order and
requires distinct destinations.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Source.Closure

def Layout.entriesVector {parent : Scope} {captures : List Capture}
    (layout : Layout parent captures) : Vector (Entry parent) captures.length :=
  ⟨layout.entries.toArray, by simpa using congrArg List.length layout.inOrder⟩

namespace Frame

def ordinaryNames (scope : Scope) : List Name :=
  (scope.context.parameters ++ scope.context.assigned.reverse).eraseDups.filter fun name =>
    decide (scope.access name = some .local ∧ name ∉ scope.cells)

/-- A parameter initializes either an ordinary local or an owned cell. -/
abbrev Destination (scope : Scope) :=
  Sum (Fin (ordinaryNames scope).length) (Fin scope.cells.length)

def Destination.nameAt (scope : Scope) : Destination scope → Name
  | .inl index => (ordinaryNames scope)[index]
  | .inr index => scope.cells[index]

structure ParameterSlot (scope : Scope) where
  name : Name
  destination : Destination scope
  lookup_eq : Destination.nameAt scope destination = name
  access_eq : scope.access name = some .local

def findName? (names : List Name) (name : Name) :
    Option {index : Fin names.length // names[index] = name} :=
  let selected := names.findFinIdx? (fun candidate => decide (candidate = name))
  selected.pmap (p := fun index => selected = some index)
    (fun index found => ⟨index, of_decide_eq_true (List.findFinIdx?_eq_some_iff.mp found).1⟩)
    (fun _ found => Option.mem_def.mp found)

def ParameterSlot.find? (scope : Scope) (name : Name) :
    Option {slot : ParameterSlot scope // slot.name = name} :=
  if access : scope.access name = some .local then
    match findName? scope.cells name with
    | some slot => some ⟨⟨name, .inr slot.val, slot.property, access⟩, rfl⟩
    | none =>
      (findName? (ordinaryNames scope) name).map fun slot =>
        ⟨⟨name, .inl slot.val, slot.property, access⟩, rfl⟩
  else none

def orderParameters (scope : Scope) : (names : List Name) →
    Option {entries : List (ParameterSlot scope) // entries.map ParameterSlot.name = names}
  | [] => some ⟨[], rfl⟩
  | name :: rest => do
    let first ← ParameterSlot.find? scope name
    let tail ← orderParameters scope rest
    return ⟨first.val :: tail.val, by simp [first.property, tail.property]⟩

structure ParameterLayout (scope : Scope) where
  entries : List (ParameterSlot scope)
  inOrder : entries.map ParameterSlot.name = scope.context.parameters
  distinct : (entries.map ParameterSlot.destination).Nodup

def parameterLayout? (scope : Scope) : Option (ParameterLayout scope) := do
  let ordered ← orderParameters scope scope.context.parameters
  if distinct : (ordered.val.map ParameterSlot.destination).Nodup then
    return ⟨ordered.val, ordered.property, distinct⟩
  else none

def ParameterLayout.destinations {scope : Scope} (layout : ParameterLayout scope) :
    Vector (Destination scope) scope.context.parameters.length :=
  ⟨(layout.entries.map ParameterSlot.destination).toArray,
    by simpa using congrArg List.length layout.inOrder⟩

end Frame
end Silmaril.Languages.Python.Source.Closure
