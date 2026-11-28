module

public import Silmaril.Semantics.Page.Trace.Defs

/-! Fixed-size, zero-based page arrays. -/

@[expose] public section
namespace Silmaril.Semantics.Page

open ReadWrite

universe v
variable {Content : Type v} {n : Nat}

/-- A finite array with a value at every index. -/
abbrev Array (n : Nat) (Content : Type v) := Fin n → Content

/-- A finite array with allocated but uninitialized entries (none).
Indices outside its size are absent. -/
abbrev UndefArray (n : Nat) (Content : Type v) := Fin n → Option Content

def Array.embed (a : Array n Content) : UndefArray n Content := fun i => some (a i)

def UndefArray.complete (a : UndefArray n Content) (fill : Array n Content) : Array n Content :=
  fun i => (a i).getD (fill i)

/-- View in the ordinary page store, with exact distinctions between absent,
uninitialized and defined slots. -/
def UndefArray.toMemory (a : UndefArray n Content) : MapMemory Nat Content :=
  fun page => if h : page < n then
    match a ⟨page, h⟩ with
    | none => .undef
    | some value => .defined value
  else .absent

def Array.access (n : Nat) (Content : Type v) : Access Nat Content (Array n Content) where
  read a page := if h : page < n then some (a ⟨page, h⟩) else none
  write a page value := if h : page < n then some (override a ⟨page, h⟩ value) else none

def UndefArray.access (n : Nat) (Content : Type v) : Access Nat Content (UndefArray n Content) where
  read a page := if h : page < n then a ⟨page, h⟩ else none
  write a page value := if h : page < n then some (override a ⟨page, h⟩ (some value)) else none

/-- The witness is an initial, fully defined array of the given size. -/
def Array.Satisfiable (n : Nat) (trace : Trace Nat Content) : Prop :=
  trace.Satisfiable (Array.access n Content)

/-- The witness is an initial array of the given size admitting UNDEF. -/
def UndefArray.Satisfiable (n : Nat) (trace : Trace Nat Content) : Prop :=
  trace.Satisfiable (UndefArray.access n Content)

def Array.InBounds (n : Nat) (trace : Trace Nat Content) : Prop :=
  ∀ page, trace.Footprint page → page < n

end Silmaril.Semantics.Page
