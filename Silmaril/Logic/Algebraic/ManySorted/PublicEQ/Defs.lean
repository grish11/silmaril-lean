module

public import Silmaril.Logic.Algebraic.ManySorted.Defs
public import Silmaril.Logic.Institution.Examples.Equational

@[expose] public section
namespace Silmaril.Logic.Algebraic.ManySorted.PublicEQ
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.Institution.Examples
variable {S : Type} {A B : Signature S}

def signature (A : Signature S) : EQ.Signature := ⟨S, A.operations⟩
def signatureMap (f : A ⟶ B) : signature A ⟶ signature B := ⟨id, f.operations⟩
def signatures (S : Type) : Signature S ⥤ EQ.Signature where
  obj := signature
  map := signatureMap
  map_id _ := rfl
  map_comp _ _ := rfl

def toTerm {k} {Γ : Fin k → S} {s} : EQ.Term (signature A) Γ s → Term A Γ s
  | .var i => .var i
  | .app op args => .app op (fun i => toTerm (args i))
def fromTerm {k} {Γ : Fin k → S} {s} : Term A Γ s → EQ.Term (signature A) Γ s
  | .var i => .var i
  | .app op args => .app op (fun i => fromTerm (args i))

def toEquation (e : EQ.Equation (signature A)) : Equation A :=
  ⟨e.k, e.ctx, e.sort, toTerm e.lhs, toTerm e.rhs⟩
def fromEquation (e : Equation A) : EQ.Equation (signature A) :=
  ⟨e.variableCount, e.context, e.sort, fromTerm e.lhs, fromTerm e.rhs⟩

def toModel (M : EQ.Algebra (signature A)) : Model A := ⟨M.carrier, M.op⟩
def fromModel (M : Model A) : EQ.Algebra (signature A) := ⟨M.carrier, M.operation⟩
def toModels (A : Signature S) : EQ.Algebra (signature A) ⥤ Model A where
  obj := toModel
  map h := ⟨h.map, h.map_op⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def fromModels (A : Signature S) : Model A ⥤ EQ.Algebra (signature A) where
  obj := fromModel
  map h := ⟨h.map, h.operation⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.Logic.Algebraic.ManySorted.PublicEQ
