module

public import Silmaril.ProofFormats.DaslSyntax.Defs
public import Silmaril.Logic.Institution.Examples.Unsorted.SExp.Thms
public import Silmaril.Logic.Consequence.FirstOrder.Derivation.Defs

/-! The one-sorted institution, with explicit, reversible signature labels. -/

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax.FOL

open Silmaril.Formats.Dasl
open Silmaril.Logic.Institution.Examples.UFOL
open CategoryTheory

/-- A label table and an arity-preserving codec in both directions. Operation and relation
namespaces are disjoint by their tags. A label in either namespace determines its arity. -/
structure Labels (sig : Signature) where
  opArity : String → Option Nat
  relArity : String → Option Nat
  symbols : sig ≅ named opArity relArity

def Labels.identity (opArity relArity : String → Option Nat) : Labels (named opArity relArity) :=
  ⟨opArity, relArity, Iso.refl _⟩

def slots : InlinePrefix := fun _ tag => if tag = "var" || tag = "app" || tag = "rel" then 2 else 1

variable {sig : Signature}

def term (labels : Labels sig) (depth : Nat) : Syntax (Term sig depth) :=
  ⟨{ encode := fun term => SExp.encodeTerm (term.map labels.symbols.hom)
     decode? := fun form => (SExp.readTerm? labels.opArity labels.relArity depth form).map (·.map labels.symbols.inv)
     recovers term := by rw [SExp.readTerm?_encodeTerm, Option.map_some, ← Term.map_comp, Iso.hom_inv_id, Term.map_id] },
    slots⟩

def formula (labels : Labels sig) (depth : Nat) : Syntax (Formula sig depth) :=
  ⟨{ encode := fun form => SExp.encodeFormula (form.map labels.symbols.hom)
     decode? := fun form => (SExp.decodeFormula labels.opArity labels.relArity depth form).map (·.map labels.symbols.inv)
     recovers form := by
       rw [SExp.decodeFormula_eq_some_iff.mpr rfl, Option.map_some, ← Formula.map_comp, Iso.hom_inv_id, Formula.map_id] },
    slots⟩

variable {Name : Type} (store : Store Name) (labels : Labels sig)

def sentences : Set Name := (formula labels 0).namesWhere store (fun _ => True)

def trueIn (model : Structure sig) : Set Name :=
  (formula labels 0).namesWhere store (Sentence.Holds model)

/-- Truth in every model of this signature (logical validity), not derivability. -/
def valid : Set Name := (formula labels 0).namesWhere store (fun sentence => ∀ model, Sentence.Holds model sentence)

def theorems [∀ arity, DecidableEq (sig.Op arity)] [∀ arity, DecidableEq (sig.Rel arity)] : Set Name :=
  (formula labels 0).namesWhere store (Consequence.FirstOrder.ND.treeDerives sig [])

end Silmaril.ProofFormats.DaslSyntax.FOL
