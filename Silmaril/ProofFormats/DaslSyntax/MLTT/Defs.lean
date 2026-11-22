module

public import Silmaril.ProofFormats.DaslSyntax.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SExp.Thms

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax.MLTT

open Silmaril.Formats.Dasl
open Silmaril.Logic.TypeTheory.ExtensionalMLTT

def termSlots : InlinePrefix := fun _ tag =>
  if tag = "fv" || tag = "bv" || tag = "univ" then 2 else 1

def tm (depth : Nat) : Syntax (ETm depth) :=
  ⟨⟨SExp.encodeTm, SExp.readTm? depth, SExp.readTm?_encodeTm⟩, termSlots⟩

/-- Type expressions have the same raw grammar as terms. Formation is a separate judgment. -/
abbrev ty : Syntax (ETm 0) := tm 0

/-- Declarations are oldest first. At each declaration only the type slot is a child. -/
def ctxSlots : InlinePrefix := fun path tag =>
  match path with
  | [_] => 1
  | _ => termSlots path tag

def ctx : Syntax ECtx := ⟨⟨SExp.encodeCtx, SExp.readCtx?, SExp.readCtx?_encodeCtx⟩, ctxSlots⟩

def wellFormed (context : ECtx) : Prop := ECtx.JEq context .unit .star .star

def formsType (context : ECtx) (type : ETm 0) : Prop :=
  wellFormed context ∧ ∃ level, ECtx.JEq context (.univ level) type type

def checks (context : ECtx) (type term : ETm 0) : Prop :=
  wellFormed context ∧ ECtx.JEq context type term term

/-- The witness is a term, not a term name. No search or decision procedure is implied. -/
def inhabits (context : ECtx) (type : ETm 0) : Prop := ∃ term, checks context type term

variable {Name : Type} (store : Store Name)

def typing (context term type : Name) : Prop :=
  Semantics.Naming.Lift.rel (coordinates := [ctx.named store, (tm 0).named store, ty.named store])
    (fun args => checks args.1 args.2.2.1 args.2.1) (context, term, type, ())

def wellTyped (context : ECtx) (type : ETm 0) : Set Name :=
  (tm 0).namesWhere store (checks context type)

def types (context : ECtx) : Set Name := ty.namesWhere store (formsType context)

def inhabitedTypes (context : ECtx) : Set Name := ty.namesWhere store (inhabits context)

def inhabitance : Consequence.System Name Name := system (ctx.named store) (ty.named store) inhabits

def lenNat (context : Name) (size : Nat) : Prop :=
  Lift.lengthNat (ctx.named store) (fun decoded => (SExp.ctxDecls decoded).length) context size

def lenI64 (context : Name) (size : Value) : Prop :=
  Lift.lengthI64 (ctx.named store) (fun decoded => (SExp.ctxDecls decoded).length) context size

end Silmaril.ProofFormats.DaslSyntax.MLTT
