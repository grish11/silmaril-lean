module

public import Silmaril.Logic.Smt.Uflia.SExpr.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete

/-- A concrete representative retains its actual input bytes and both executable
reader/decoder equalities. It is not an alias for an abstract formula. -/
structure Accepted (E : Environment) where
  bytes : List UInt8
  expression : Expr
  formula : Formula E.signature
  read : readForms bytes = some [expression]
  decoded : decodeFormula? E expression = some formula

abbrev Representative := Accepted

/-- Representatives are identified exactly when their actual decoded formulas
coincide; byte and expression witnesses remain in each representative. -/
def acceptedSetoid (E : Environment) : Setoid (Accepted E) where
  r a b := a.formula = b.formula
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

def Sentence (E : Environment) := Quotient (acceptedSetoid E)

namespace Sentence

def mk {E : Environment} (a : Accepted E) : Sentence E := Quotient.mk _ a

/-- Well-defined projection of the actual accepted-representative quotient. -/
def decode {E : Environment} : Sentence E → Formula E.signature :=
  Quotient.lift (fun a => a.formula) (fun _ _ h => h)

end Sentence

/-- Satisfaction uses the existing model and its interpretation of the exact
formula computed by representative decoding. -/
noncomputable def Holds {E : Environment} (M : Uflia.Model E.signature) (s : Sentence E) : Prop :=
  M.Holds s.decode

/-- Direct byte semantics uses the actual reader and typed formula decoder. -/
noncomputable def ByteHolds (E : Environment) (bytes : List UInt8)
    (M : Uflia.Model E.signature) : Prop :=
  ∃ e φ, readForms bytes = some [e] ∧ decodeFormula? E e = some φ ∧ M.Holds φ

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
