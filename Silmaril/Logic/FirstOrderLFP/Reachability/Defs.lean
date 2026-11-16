module

public import Silmaril.Logic.FirstOrderLFP.Thms
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Fin

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP.Reachability
open Silmaril.Logic.Institution.Examples

inductive EdgeSymbol : (n : Nat) → (Fin n → Unit) → Type
  | edge : EdgeSymbol 2 (fun _ => ())

abbrev signature : Signature where
  S := Unit
  Op := fun _ _ _ => Empty
  Rel := EdgeSymbol

/-- No finiteness or inhabitedness assumption is made on the carrier. -/
abbrev model (A : Type) (E : A → A → Prop) : Model signature := ⟨{
  carrier := fun _ => A
  op := fun o => o.elim
  rel := fun r args => match r with | .edge => E (args 0) (args 1) }⟩

abbrev context (n : Nat) : Fin n → signature.S := fun _ => ()
abbrev profiles (n : Nat) : Fin 1 → Profile signature := fun _ => ⟨n, context n⟩
abbrev emptyProfiles : Fin 0 → Profile signature := (profiles 1) ∘ Fin.succ

def varTerm {k : Nat} (i : Fin k) : EQ.Term signature.toSignature (context k) () := .var i

def edge {r k : Nat} {P : Fin r → Profile signature} (i j : Fin k) :
    Formula signature P (context k) :=
  .base (.rel .edge ![varTerm i, varTerm j])

/-- Binary transitive closure: μR(x,y). E(x,y) ∨ ∃z. R(x,z) ∧ E(z,y). -/
def binaryBody : Formula signature (profiles 2) (context 2) :=
  .disj (edge 0 1) (.ex (.conj (.pred 0 ![varTerm 1, varTerm 0]) (edge 0 2)))

/-- The binary body under a two-object ambient context, whose parameters it ignores. -/
def binaryParameterBody : Formula signature (profiles 2) (context 4) :=
  .disj (edge 0 1) (.ex (.conj (.pred 0 ![varTerm 1, varTerm 0]) (edge 0 2)))

/-- The binary least-fixed-point formula applied to source and target terms. -/
def transitive : Formula signature ((profiles 2) ∘ Fin.succ) (context 2) :=
  .lfp (by rfl) (by rfl) binaryParameterBody ![varTerm 0, varTerm 1]

/-- Unary reachability to a captured target: μR(x). x=t ∨ ∃z. E(x,z) ∧ R(z). -/
def parameterBody : Formula signature (profiles 1) (context 3) :=
  .disj (.base (.eq (varTerm 0) (varTerm 2)))
    (.ex (.conj (edge 1 0) (.pred 0 ![varTerm 0])))

/-- The outer variables are source and target. The target remains a captured parameter. -/
def reaches : Formula signature emptyProfiles (context 2) :=
  .lfp (by rfl) (by rfl) parameterBody ![varTerm 0]

end Silmaril.Logic.FirstOrderLFP.Reachability
