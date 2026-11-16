module

public import Silmaril.Logic.Egg.Core.FirstOrder
public import Silmaril.Logic.Egglog.Core.Prolog

@[expose] public section
namespace Silmaril.Logic.Egglog.Core.Egg
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples

/-- Preserve every sorted constructor; introduce no predicates or partial tables. -/
abbrev signature (S : EQ.Signature) : Core.Signature := Prolog.signature (EQtoFOL.sig S)

def signatures : EQ.Signature ⥤ Core.Signature := EQtoFOL.sigFunctor ⋙ Prolog.signatures

/-- Decode actual table-free models and all their actual homomorphisms. -/
def models (S : EQ.Signature) : Core.Model (signature S) ⥤ EQ.Algebra S :=
  Prolog.models (EQtoFOL.sig S) ⋙ EQtoFOL.mod S

def atom {S : EQ.Signature} {n : Nat} {Γ : Fin n → S.S}
    (e : Silmaril.Logic.Egg.Core.Equality S Γ) : Core.Atom (signature S) Γ := .equal e

/-- Keep all equality guards and the equality conclusion, in their original order. -/
def sentence {S : EQ.Signature} (r : Silmaril.Logic.Egg.Core.Rule S) : Core.Sentence (signature S) :=
  .rule ⟨r.scope, r.context, r.guards.map atom, atom r.conclusion⟩

/-- Expand an arbitrary algebra, without free-constructor or unique-name assumptions. -/
def expansion {S : EQ.Signature} (M : EQ.Algebra S) : Core.Model (signature S) :=
  Prolog.expansion (EQtoFOL.expansion M)

/-- Every algebra hom lifts; predicates and partial-table symbols are empty. -/
def liftHom {S : EQ.Signature} {M N : Core.Model (signature S)}
    (h : (models S).obj M ⟶ (models S).obj N) : M ⟶ N where
  map := h.map
  map_op := h.map_op
  map_rel r := r.elim
  row f := f.elim

end Silmaril.Logic.Egglog.Core.Egg
