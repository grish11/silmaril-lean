module

public import Silmaril.ProofFormats.DaslSyntax.Defs
public import Silmaril.Formats.Dasl.Encode.Thms
public import Silmaril.Logic.HOLLight.SExp.Thms
public import Silmaril.Logic.HOLLight.Semantics.Validity
public import Silmaril.Formats.Dasl.Lift.Set.Defs

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax.HOL

open Silmaril.Formats.Dasl
open Silmaril.Logic.HOLLight

universe u

def slots : InlinePrefix := fun _ tag =>
  if tag = "tyvar" || tag = "tyapp" || tag = "bvar" || tag = "fvar" || tag = "const" then 2 else 1

def ty : Syntax Ty := ⟨⟨SExp.encodeTy, SExp.decodeTy, SExp.decodeTy_encodeTy⟩, slots⟩
def tm : Syntax Tm := ⟨ofSExpCodec SExp.codec, slots⟩

/-- The first type is the type of bound index zero. This is not a hypothesis set. -/
def ctx : Syntax (List Ty) := ⟨ty.codec.listCodec.then (taggedList "ctx"), slots⟩

/-- An ordered spelling of assumptions; interpretation can quotient by list membership. -/
def assumptions : Syntax (List Tm) := ⟨tm.codec.listCodec.then (taggedList "hyps"), slots⟩

variable {Name : Type} (store : Store Name)

def typing (sig : Signature) (context term type : Name) : Prop :=
  Semantics.Naming.Lift.rel (coordinates := [ctx.named store, tm.named store, ty.named store])
    (fun args => HasType sig args.1 args.2.1 args.2.2.1) (context, term, type, ())

def wellTyped (sig : Signature) (context : List Ty) (type : Ty) : Set Name :=
  tm.namesWhere store (fun term => HasType sig context term type)

def propositions (sig : Signature) : Set Name := wellTyped store sig [] .bool

def theorems (sig : Signature) (theory : Theory) : Set Name :=
  tm.namesWhere store (Derives sig theory ∅)

/-- Valid in the supplied model at all valuations; not kernel provability. -/
def validIn {sig : Signature} (model : Model.{u} sig) : Set Name :=
  tm.namesWhere store (fun term => HasType sig [] term .bool ∧ Valid model term)

def derives (sig : Signature) (theory : Theory) : Consequence.System Name Name :=
  system (assumptions.named store) (tm.named store) (fun premises term => Derives sig theory premises.toFinset term)

/-- Use an independently justified hypothesis-name resolver, e.g. an ordered set store. -/
def derivesWith (resolved : Name → Hyps → Prop) (sig : Signature) (theory : Theory) :
    Consequence.System Name Name :=
  system (.encoded resolved) (tm.named store) (Derives sig theory)

def derivesFromSet (layout : Value → Hyps → Prop) (sig : Signature) (theory : Theory) :
    Consequence.System Name Name :=
  derivesWith store (Lift.name store layout).represents sig theory

def orderedAssumptions {Key : Type} [LinearOrder Key] (label : Encode.TotalCodec Tm Key)
    (key : Encode.TotalCodec Key Value) : Value → Hyps → Prop := Lift.codedSet (Lift.orderedSet key) label

def semantic {sig : Signature} (model : Model.{u} sig) : Consequence.System Hyps Tm :=
  fun premises term => TypedHyps sig [] premises ∧ HasType sig [] term .bool ∧ Entails model premises term

def entails {sig : Signature} (model : Model.{u} sig) : Consequence.System Name Name :=
  system (assumptions.named store) (tm.named store) (fun premises => semantic model premises.toFinset)

def entailsWith (resolved : Name → Hyps → Prop) {sig : Signature} (model : Model.{u} sig) :
    Consequence.System Name Name :=
  system (.encoded resolved) (tm.named store) (semantic model)

def entailsFromSet (layout : Value → Hyps → Prop) {sig : Signature} (model : Model.{u} sig) :
    Consequence.System Name Name :=
  entailsWith store (Lift.name store layout).represents model

end Silmaril.ProofFormats.DaslSyntax.HOL
