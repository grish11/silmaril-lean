module

public import Silmaril.Languages.Python.Source.Scope.Defs

/-! # Ordered closure captures for a Python source scope

Each capture of a child block comes from either a locally owned cell of its
parent or a forwarded capture. The source origin selects the slot family.
The layout retains the child's order and the exact lookup at each slot.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Source.Closure

def Available (parent : Scope) (capture : Capture) : Prop :=
  if capture.origin = parent.context.path then capture.name ∈ parent.cells
  else capture ∈ parent.captures

inductive Slot (parent : Scope) (capture : Capture) where
  | owned (index : Fin parent.cells.length)
      (origin : capture.origin = parent.context.path) (lookup : parent.cells[index] = capture.name)
  | forwarded (index : Fin parent.captures.length)
      (origin : capture.origin ≠ parent.context.path) (lookup : parent.captures[index] = capture)

def Slot.cell {Cell : Type} {parent : Scope} {capture : Capture}
    (slot : Slot parent capture) (owned : Fin parent.cells.length → Cell)
    (incoming : Fin parent.captures.length → Cell) : Cell :=
  match slot with
  | .owned index _ _ => owned index
  | .forwarded index _ _ => incoming index

def Slot.find? (parent : Scope) (capture : Capture) : Option (Slot parent capture) :=
  if owner : capture.origin = parent.context.path then
    let selected := parent.cells.findFinIdx? (fun name => decide (name = capture.name))
    selected.pmap (p := fun index => selected = some index)
      (fun index found => .owned index owner (of_decide_eq_true (List.findFinIdx?_eq_some_iff.mp found).1))
      (fun _ found => Option.mem_def.mp found)
  else
    let selected := parent.captures.findFinIdx? (fun entry => decide (entry = capture))
    selected.pmap (p := fun index => selected = some index)
      (fun index found =>
        .forwarded index owner (of_decide_eq_true (List.findFinIdx?_eq_some_iff.mp found).1))
      (fun _ found => Option.mem_def.mp found)

structure Entry (parent : Scope) where
  capture : Capture
  slot : Slot parent capture

structure Layout (parent : Scope) (captures : List Capture) where
  entries : List (Entry parent)
  inOrder : entries.map Entry.capture = captures

/-- Read the child's capture vector from the parent's existing cell identities. -/
def Layout.cells {Cell : Type} {parent : Scope} {captures : List Capture}
    (layout : Layout parent captures) (owned : Fin parent.cells.length → Cell)
    (incoming : Fin parent.captures.length → Cell) : List Cell :=
  layout.entries.map (fun entry => entry.slot.cell owned incoming)

/-- Locate parent slots for the capture vector of a child scope. -/
def layout? (parent : Scope) : (captures : List Capture) → Option (Layout parent captures)
  | [] => some ⟨[], rfl⟩
  | capture :: rest => do
    let slot ← Slot.find? parent capture
    let tail ← layout? parent rest
    return ⟨⟨capture, slot⟩ :: tail.entries, by simp [tail.inOrder]⟩

end Silmaril.Languages.Python.Source.Closure
