module

public import Silmaril.Formats.Dasl.Language.Defs
public import Silmaril.ProofFormats.DaslSyntax.HOL.Defs
public import Silmaril.ProofFormats.DaslSyntax.MLTT.Defs

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax.Database

open Silmaril.Formats.Dasl (Value)
open Silmaril.Semantics.Naming (Relation)
open Silmaril.Semantics.Naming.Lift (Coordinate where_)

/-- A first-class consequence system on abstract DASL values, with independent
representations for contexts and conclusions. No byte or digest interpretation is needed. -/
def valueSystem {Context Statement : Type} (context : Relation Value Context)
    (statement : Relation Value Statement) (source : Consequence.System Context Statement) :
    Consequence.System Value Value := system (.encoded context) (.encoded statement) source

/-- Specialize two coordinates to arbitrary name relations, not necessarily in one store. -/
def namedSystem {ContextName StatementName Context Statement : Type}
    (context : Relation ContextName Context) (statement : Relation StatementName Statement)
    (source : Consequence.System Context Statement) : Consequence.System ContextName StatementName :=
  system (.encoded context) (.encoded statement) source

/-- A three-column table for given typing. Coordinates can be names, direct syntax, or encodings. -/
def typingTable (context term type : Coordinate)
    (checks : context.Meaning → term.Meaning → type.Meaning → Prop)
    (contextInput : context.Surface) (termInput : term.Surface) (typeInput : type.Surface) : Prop :=
  Silmaril.Semantics.Naming.Lift.rel (coordinates := [context, term, type])
    (fun args => checks args.1 args.2.1 args.2.2.1) (contextInput, termInput, typeInput, ())

/-- The binary projection checks a term at a type in one stated context. -/
def typingAt (term type : Coordinate) (checks : term.Meaning → type.Meaning → Prop) :
    Consequence.System term.Surface type.Surface := system term type checks

namespace HOL

open Silmaril.Logic.HOLLight

variable {ContextName TermName TypeName : Type}

universe u

def derives (hypotheses : Relation ContextName Hyps) (terms : Relation TermName Tm)
    (sig : Signature) (theory : Theory) : Consequence.System ContextName TermName :=
  namedSystem hypotheses terms (Derives sig theory)

def entails (hypotheses : Relation ContextName Hyps) (terms : Relation TermName Tm)
    {sig : Signature} (model : Model.{u} sig) : Consequence.System ContextName TermName :=
  namedSystem hypotheses terms (DaslSyntax.HOL.semantic model)

def listAssumptions (terms : Relation TermName Tm) : Relation (List TermName) Hyps :=
  fun names hyps => ∃ decoded, List.Forall₂ terms names decoded ∧ decoded.toFinset = hyps

/-- A finite input uses a listing of exactly its members. Binding is needed to
compare arbitrary listings that may repeat a name, not to define membership. -/
def finiteAssumptions (terms : Relation TermName Tm) : Relation (Finset TermName) Hyps :=
  fun names hyps => ∃ listed, (∀ name, name ∈ listed ↔ name ∈ names) ∧ listAssumptions terms listed hyps

def derivesList (terms : Relation TermName Tm) (sig : Signature) (theory : Theory) :
    Consequence.System (List TermName) TermName := derives (listAssumptions terms) terms sig theory

def derivesFinite (terms : Relation TermName Tm) (sig : Signature) (theory : Theory) :
    Consequence.System (Finset TermName) TermName := derives (finiteAssumptions terms) terms sig theory

/-- Closed in term variables; schematic type parameters are permitted. -/
def ClosedProof (sig : Signature) (theory : Theory) (term : Tm) : Prop :=
  term.Closed ∧ term.freeVars = [] ∧ Derives sig theory ∅ term

def closedTheorems (terms : Relation TermName Tm) (sig : Signature) (theory : Theory) : Set TermName :=
  where_ (.encoded terms) (ClosedProof sig theory)

def propositions (terms : Relation TermName Tm) (sig : Signature) : Set TermName :=
  where_ (.encoded terms) (fun term => HasType sig [] term .bool)

def validIn (terms : Relation TermName Tm) {sig : Signature} (model : Model.{u} sig) : Set TermName :=
  where_ (.encoded terms) (fun term => HasType sig [] term .bool ∧ Valid model term)

def validTypes (types : Relation TypeName Ty) (sig : Signature) : Set TypeName :=
  where_ (.encoded types) (Ty.WellFormed sig.tyOps)

def typing (contexts : Relation ContextName (List Ty)) (terms : Relation TermName Tm)
    (types : Relation TypeName Ty) (sig : Signature) : ContextName → TermName → TypeName → Prop :=
  typingTable (.encoded contexts) (.encoded terms) (.encoded types) (HasType sig)

def typingAt (terms : Relation TermName Tm) (types : Relation TypeName Ty) (sig : Signature)
    (context : List Ty) : Consequence.System TermName TypeName :=
  Database.typingAt (.encoded terms) (.encoded types) (HasType sig context)

end HOL

namespace MLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

variable {ContextName TermName TypeName : Type}

def formation (contexts : Relation ContextName ECtx) (types : Relation TypeName (ETm 0)) :
    Consequence.System ContextName TypeName := namedSystem contexts types DaslSyntax.MLTT.formsType

/-- No term-name coordinate: any kernel witness in the resolved context suffices. -/
def inhabitance (contexts : Relation ContextName ECtx) (types : Relation TypeName (ETm 0)) :
    Consequence.System ContextName TypeName := namedSystem contexts types DaslSyntax.MLTT.inhabits

def typing (contexts : Relation ContextName ECtx) (terms : Relation TermName (ETm 0))
    (types : Relation TypeName (ETm 0)) : ContextName → TermName → TypeName → Prop :=
  typingTable (.encoded contexts) (.encoded terms) (.encoded types)
    (fun context term type => DaslSyntax.MLTT.checks context type term)

def typingAt (terms : Relation TermName (ETm 0)) (types : Relation TypeName (ETm 0))
    (context : ECtx) : Consequence.System TermName TypeName :=
  Database.typingAt (.encoded terms) (.encoded types) (fun term type => DaslSyntax.MLTT.checks context type term)

def wellTyped (terms : Relation TermName (ETm 0)) (context : ECtx) (type : ETm 0) : Set TermName :=
  where_ (.encoded terms) (DaslSyntax.MLTT.checks context type)

end MLTT

end Silmaril.ProofFormats.DaslSyntax.Database
