module

public import Mathlib.Data.Finset.Basic
public import Silmaril.Semantics.Naming.Defs

/-! The ATProto data model, independent of the wire representation and Lexicon.
Use `Empty` for impossible edges and `Unit` for erased names. Dicts are unordered,
and lists carry a fixed length. Neither form permits absent inline children. -/

@[expose] public section

namespace Silmaril.Formats.Dasl

inductive Link (Name : Type) where
  | obj (name : Name)
  | blob (name : Name)
  deriving DecidableEq

def Link.map {Name Next : Type} (rename : Name → Next) : Link Name → Link Next
  | .obj name => .obj (rename name)
  | .blob name => .blob (rename name)

inductive Tree (Ref Name : Type) where
  | ref (link : Ref)
  | obj (name : Name) (target : Tree Ref Name)
  | blob (name : Name) (target : ByteArray)
  | dict (keys : Finset String) (values : ↥keys → Tree Ref Name)
  | list (len : Nat) (values : Fin len → Tree Ref Name)
  | i64 (bits : UInt64)
  | bytes (value : ByteArray)
  | string (value : String)
  | bool (value : Bool)
  | null

abbrev Value := Tree Empty Unit
abbrev Named (Name : Type) := Tree Empty Name
abbrev Partial (Name : Type) := Tree (Link Name) Name
abbrev Mixed (Name : Type) := Tree (Link Name) Unit
abbrev Shallow (Name : Type) := Tree (Link Name) Empty

def Value.obj (target : Value) : Value := Tree.obj () target
def Value.blob (target : ByteArray) : Value := Tree.blob () target

def Tree.map {Ref Name Ref' Name' : Type} (refs : Ref → Ref') (names : Name → Name') :
    Tree Ref Name → Tree Ref' Name'
  | .ref link => .ref (refs link)
  | .obj name child => .obj (names name) (Tree.map refs names child)
  | .blob name payload => .blob (names name) payload
  | .dict keys values => .dict keys fun key => Tree.map refs names (values key)
  | .list len values => .list len fun index => Tree.map refs names (values index)
  | .i64 bits => .i64 bits
  | .bytes payload => .bytes payload
  | .string text => .string text
  | .bool value => .bool value
  | .null => .null

def Named.erase {Name : Type} : Named Name → Value := Tree.map id (fun _ => ())
def Named.embed {Name : Type} : Named Name → Partial Name := Tree.map Empty.elim id
def Partial.erase {Name : Type} : Partial Name → Mixed Name := Tree.map id (fun _ => ())
def Shallow.embed {Name : Type} : Shallow Name → Partial Name := Tree.map id Empty.elim
def Shallow.map {Name Next : Type} (rename : Name → Next) : Shallow Name → Shallow Next :=
  Tree.map (Link.map rename) id

/-- Replace expanded targets by names, stopping at CAS boundaries. -/
def Partial.shallow {Name : Type} : Partial Name → Shallow Name
  | .ref link => .ref link
  | .obj name _ => .ref (.obj name)
  | .blob name _ => .ref (.blob name)
  | .dict keys values => .dict keys fun key => shallow (values key)
  | .list len values => .list len fun index => shallow (values index)
  | .i64 bits => .i64 bits
  | .bytes payload => .bytes payload
  | .string text => .string text
  | .bool value => .bool value
  | .null => .null

/-- Information order: inline shape and existing names are fixed. Only references can be
resolved, and resolved object children can be further refined. -/
inductive Extends {Name : Type} : Partial Name → Partial Name → Prop where
  | same (tree) : Extends tree tree
  | openObj (name) (target) : Extends (.ref (.obj name)) (.obj name target)
  | openBlob (name) (target) : Extends (.ref (.blob name)) (.blob name target)
  | obj (name) {left right} : Extends left right → Extends (.obj name left) (.obj name right)
  | dict {keys : Finset String} {left right : ↥keys → Partial Name} :
      (∀ key, Extends (left key) (right key)) → Extends (.dict keys left) (.dict keys right)
  | list {len} {left right : Fin len → Partial Name} :
      (∀ index, Extends (left index) (right index)) → Extends (.list len left) (.list len right)

/-- All names mentioned, including unresolved names. `recursive = false` traverses inline
containers but does not enter CAS targets. -/
def Partial.links {Name : Type} (recursive : Bool) : Partial Name → Set (Link Name)
  | .ref link => {link}
  | .obj name target => if recursive then {link | link = .obj name ∨ link ∈ links recursive target}
                        else {.obj name}
  | .blob name _ => {.blob name}
  | .dict _ values => {link | ∃ key, link ∈ links recursive (values key)}
  | .list _ values => {link | ∃ index, link ∈ links recursive (values index)}
  | _ => ∅

open Silmaril.Semantics.Naming in
/-- Known bindings only, recursively. Object witnesses use shallow projections, not the
possibly different dereference choices made at separate occurrences. -/
def Partial.bindings {Name : Type} : Partial Name → Stores Name (Shallow Name) ByteArray
  | .obj name target =>
      let children := bindings target
      ⟨fun key value => (key = name ∧ value = shallow target) ∨ children.objects key value,
        children.blobs⟩
  | .blob name bytes => ⟨fun _ _ => False, fun key value => key = name ∧ value = bytes⟩
  | .dict _ values => ⟨fun name value => ∃ key, (bindings (values key)).objects name value,
                       fun name value => ∃ key, (bindings (values key)).blobs name value⟩
  | .list _ values => ⟨fun name value => ∃ index, (bindings (values index)).objects name value,
                       fun name value => ∃ index, (bindings (values index)).blobs name value⟩
  | _ => ⟨fun _ _ => False, fun _ _ => False⟩

open Silmaril.Semantics.Naming in
def Partial.LocallyBinding {Name : Type} (tree : Partial Name) : Prop := tree.bindings.Binding

open Silmaril.Semantics.Naming in
/-- The observed payloads can be added without a collision. Missing names are permitted;
an unresolved edge does not add a binding or constrain the payload of its name. -/
def Partial.ConsistentWith {Name : Type} (tree : Partial Name)
    (store : Stores Name (Shallow Name) ByteArray) : Prop := (store.union tree.bindings).Binding

end Silmaril.Formats.Dasl
