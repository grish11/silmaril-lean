module

public import Silmaril.Formats.Dasl.Encode.Defs
public import Silmaril.Formats.Dasl.Lift.Defs
public import Silmaril.Logic.Concrete.Codec.Defs
public import Silmaril.Logic.Consequence.Defs

/-! Transport tagged S-expressions to DASL. Atoms are strings and lists remain ordered.
Only grammar-selected child slots can be placed behind object edges. -/

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax

open Silmaril.Formats.Dasl
open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete (SExpCodec)

/-- Paths consist of zero-based list indices, nearest ancestor first. -/
abbrev Path := List Nat

abbrev Placement := Path → Bool

/-- The number of inline slots at a list, including its tag, given its path and head atom. -/
abbrev InlinePrefix := Path → String → Nat

def headAtom : List SE → String
  | .atom tag :: _ => tag
  | _ => ""

def edge (policy : Placement) (path : Path) (skip index : Nat) (child : Value) : Value :=
  if skip ≤ index && policy (index :: path) then Value.obj child else child

mutual
def renderAt (slots : InlinePrefix) (policy : Placement) (path : Path) : SE → Value
  | .atom text => .string text
  | .list items => Encode.list.encode (renderItems slots policy path (slots path (headAtom items)) 0 items)

def renderItems (slots : InlinePrefix) (policy : Placement) (path : Path) (skip index : Nat) :
    List SE → List Value
  | [] => []
  | item :: rest => edge policy path skip index (renderAt slots policy (index :: path) item) ::
      renderItems slots policy path skip (index + 1) rest
end

/-- The root itself is never a wrapper. It can be stored as an object, regardless of the policy. -/
def render (slots : InlinePrefix) (policy : Placement) (form : SE) : Value :=
  renderAt slots policy [] form

def inlineAll : Placement := fun _ => false
def linkAll : Placement := fun _ => true

/-- Open expanded object edges. This is recovery, not a placement or wire validator. -/
def read : Value → Option SE
  | .string text => some (.atom text)
  | .list _ items => (List.ofFn (fun index => read (items index)) |>.mapM id).map SE.list
  | Tree.obj _ target => read target
  | _ => none

structure Syntax (Item : Type) where
  codec : Encode.TotalCodec Item SE
  slots : InlinePrefix

def ofSExpCodec {Item : Type} (codec : SExpCodec Item) : Encode.TotalCodec Item SE :=
  ⟨codec.encode, codec.decode, fun item => (codec.decode_eq_some_iff (codec.encode item) item).2 rfl⟩

/-- A list region with an inline tag and an ordered sequence of child slots. -/
def taggedList (tag : String) : Encode.TotalCodec (List SE) SE where
  encode items := .list (.atom tag :: items)
  decode? := fun
    | .list (.atom actual :: rest) => if actual = tag then some rest else none
    | _ => none
  recovers _ := ite_eq_left rfl

open Silmaril.Semantics.Naming.Lift (Coordinate) in
/-- Interpret the coordinates of an existing consequence system, without adding structural rules. -/
def system (context conclusion : Coordinate) (source : Consequence.System context.Meaning conclusion.Meaning) :
    Consequence.System context.Surface conclusion.Surface :=
  fun ctx result => Semantics.Naming.Lift.rel (coordinates := [context, conclusion])
    (fun args => source args.1 args.2.1) (ctx, result, ())

variable {Item Name : Type}

def Syntax.write (grammar : Syntax Item) (policy : Placement) (item : Item) : Value :=
  render grammar.slots policy (grammar.codec.encode item)

def Syntax.recover (grammar : Syntax Item) (value : Value) : Option Item :=
  (read value).bind grammar.codec.decode?

def Syntax.presents (grammar : Syntax Item) (policy : Placement) (value : Value) (item : Item) : Prop :=
  grammar.write policy item = value

/-- A representation in any permitted placement. Policy witnesses need not be unique. -/
def Syntax.optional (grammar : Syntax Item) (value : Value) (item : Item) : Prop :=
  ∃ policy, grammar.presents policy value item

/-- Normalize the expanded syntax. This neither allocates names nor rewrites a store. -/
def Syntax.normalize (grammar : Syntax Item) (value : Value) : Option Value :=
  (grammar.recover value).map (grammar.write linkAll)

def Syntax.names (grammar : Syntax Item) (store : Store Name) : Name → Item → Prop :=
  Semantics.Naming.push (ValueNames store) grammar.optional

def Syntax.named (grammar : Syntax Item) (store : Store Name) :
    Silmaril.Semantics.Naming.Lift.Coordinate := Formats.Dasl.Lift.name store grammar.optional

def Syntax.namesWhere (grammar : Syntax Item) (store : Store Name) (predicate : Item → Prop) : Set Name :=
  Formats.Dasl.Lift.namesWhere store grammar.optional predicate

/-- The abstract DASL language of a concrete grammar restricted by an abstract predicate. -/
def Syntax.language (grammar : Syntax Item) (predicate : Item → Prop) : Set Value :=
  {value | ∃ item, grammar.optional value item ∧ predicate item}

end Silmaril.ProofFormats.DaslSyntax
