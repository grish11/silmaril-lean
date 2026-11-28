module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
public import Silmaril.Languages.Python.Core.Module.ListObject.Defs

/-! # Flat list displays as module call operands -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ListDisplay

open Source (Name Scope)
open Core.Module (ListHeap ListObject Value)

inductive Item where
  | literal (value : Value)
  | global (name : Name)

structure Display where
  items : List Item
  negated : Bool

def literal? : Source.Expr → Option Value := exactScalarLiteral?

inductive CheckedItem (scope : Scope) : Source.Expr → Item → Prop where
  | literal {source value} (checked : literal? source = some value) :
      CheckedItem scope source (.literal value)
  | read (name : Name) (reference : GlobalReference scope name) :
      CheckedItem scope (.name name) (.global name)

def item? (scope : Scope) : (source : Source.Expr) → Option {item // CheckedItem scope source item}
  | .name name => (globalReference? scope name).map fun reference => ⟨.global name, .read name reference⟩
  | source => match checked : literal? source with
    | some value => some ⟨.literal value, .literal checked⟩
    | none => none

inductive CheckedItems (scope : Scope) : List Source.Expr → List Item → Prop where
  | nil : CheckedItems scope [] []
  | cons {source item rest items} (first : CheckedItem scope source item)
      (remaining : CheckedItems scope rest items) : CheckedItems scope (source :: rest) (item :: items)

def items? (scope : Scope) : (source : List Source.Expr) → Option {items // CheckedItems scope source items}
  | [] => some ⟨[], .nil⟩
  | first :: rest => do
    let item ← item? scope first
    let remaining ← items? scope rest
    return ⟨item.val :: remaining.val, .cons item.property remaining.property⟩

inductive Argument (scope : Scope) : List (Source.ArgumentKind × Source.Expr) → Display → Prop where
  | display {elements items} (checked : CheckedItems scope elements items) :
      Argument scope [(.positional, .list_ elements)] ⟨items, false⟩
  | negated {elements items} (checked : CheckedItems scope elements items) :
      Argument scope [(.positional, .unary .not_ (.list_ elements))] ⟨items, true⟩

def argument? (scope : Scope) : (source : List (Source.ArgumentKind × Source.Expr)) →
    Option {display // Argument scope source display}
  | [(.positional, .list_ elements)] =>
    (items? scope elements).map fun result => ⟨⟨result.val, false⟩, .display result.property⟩
  | [(.positional, .unary .not_ (.list_ elements))] =>
    (items? scope elements).map fun result => ⟨⟨result.val, true⟩, .negated result.property⟩
  | _ => none

def Item.eval {error : Type} (read : Name → Except error Value) : Item → Except error Value
  | .literal value => .ok value
  | .global name => read name

/-- Evaluate elements in order and allocate only after every element succeeds.
The negated form still evaluates and allocates the display. -/
def Display.prepare {error : Type} (display : Display) (read : Name → Except error Value) (heap : ListHeap) :
    Except error ListObject × ListHeap :=
  match display.items.mapM (Item.eval read) with
  | .error failure => (.error failure, heap)
  | .ok contents =>
    let (object, reached) := heap.allocate contents
    (.ok object, reached)

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ListDisplay
