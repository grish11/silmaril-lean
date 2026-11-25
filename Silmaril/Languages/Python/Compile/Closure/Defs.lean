module

public import Mathlib.Data.List.Nodup
public import Silmaril.Languages.Python.Core.Closure.Defs
public import Silmaril.Languages.Python.Source.Closure.Frame.Thms

/-! # Lowering Python source closure layouts to Core -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.Closure

open Source (Access BlockPath Capture Name Scope)
open Source.Closure (Entry Layout Slot)
open Source.Closure.Frame (Destination ParameterLayout ParameterSlot ordinaryNames)

def frameLayout (scope : Scope) : Core.Closure.Layout :=
  ⟨(ordinaryNames scope).length, scope.cells.length, scope.captures.length⟩

def parameterSlot (scope : Scope) :
    Destination scope → Core.Closure.ParameterSlot (frameLayout scope)
  | .inl index => .local index
  | .inr index => .owned index

theorem parameterSlot_injective (scope : Scope) : Function.Injective (parameterSlot scope) := by
  intro left right equal
  cases left <;> cases right <;> cases equal <;> rfl

def parameters {scope : Scope} (layout : ParameterLayout scope) :
    Core.Closure.Parameters (frameLayout scope) :=
  ⟨layout.destinations.toList.map (parameterSlot scope),
    List.Nodup.map (parameterSlot_injective scope) layout.destinations_distinct⟩

def parameterName (scope : Scope) :
    Core.Closure.ParameterSlot (frameLayout scope) → Name
  | .local index => (ordinaryNames scope)[index]
  | .owned index => scope.cells[index]

inductive SlotTranslation (scope : Scope) (name : Name) :
    Core.Closure.Slot (frameLayout scope) → Prop where
  | localName (parameter : ParameterSlot scope) (named : parameter.name = name) :
      SlotTranslation scope name (parameterSlot scope parameter.destination).slot
  | captured (origin : BlockPath) (index : Fin scope.captures.length)
      (resolved : scope.access name = some (.free origin))
      (lookup : scope.captures[index] = ⟨name, origin⟩) :
      SlotTranslation scope name (.capture index)

def slot? (scope : Scope) (name : Name) :
    Option {target // SlotTranslation scope name target} :=
  match access : scope.access name with
  | some .local =>
    (ParameterSlot.find? scope name).map fun ⟨entry, named⟩ =>
      ⟨(parameterSlot scope entry.destination).slot, .localName entry named⟩
  | some (.free origin) =>
    match Slot.find? scope ⟨name, origin⟩ with
    | some (.forwarded index _ lookup) => some ⟨.capture index, .captured origin index access lookup⟩
    | _ => none
  | _ => none

def captureOperand {parent : Scope} (entry : Entry parent) :
    Core.Closure.CaptureSlot (frameLayout parent) :=
  match entry.slot with
  | .owned index _ _ => .owned index
  | .forwarded index _ _ => .forwarded index

def captureOperands {parent : Scope} {captures : List Capture}
    (layout : Layout parent captures) (index : Fin captures.length) :
    Core.Closure.CaptureSlot (frameLayout parent) :=
  captureOperand (layout.entriesVector.get index)

def codeRef (child : Scope) (key : Nat) : Core.Closure.CodeRef :=
  ⟨key, frameLayout child⟩

/-- Construct a Core closure using exactly the parent's existing cell identities. -/
def function {parent child : Scope} (key : Nat) (layout : Layout parent child.captures)
    (frame : Core.Closure.Frame (frameLayout parent)) : Core.Closure.Function :=
  Core.Closure.Function.ofCaptureList (codeRef child key)
    (layout.cells frame.owned frame.captures) (layout.cells_length frame.owned frame.captures)

end Silmaril.Languages.Python.Compile.Closure
