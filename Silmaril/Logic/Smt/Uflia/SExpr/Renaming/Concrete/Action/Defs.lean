module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Normalization.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Legality.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Category.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
open CategoryTheory Silmaril.Logic.Algebraic
open Silmaril.Logic.Smt.SExpr
variable {E F G : Environment}

/-- Successful actual decoding guarantees that executable normalization returns
an expression; this proof only discharges the extractor's erased precondition. -/
theorem Accepted.normalizationPresent (a : Accepted E) (f : NameMap E F) :
    (normalize? E f.rename a.expression).isSome := by
  obtain ⟨output, hn, _⟩ := normalizeFormula_success f a.expression a.formula a.decoded
  simp only [hn, Option.isSome_some]

/-- Extract the result of the actual executable normalizer, without a choice
oracle or a replacement abstract syntax representation. -/
def Accepted.normalizedExpression (a : Accepted E) (f : NameMap E F) : Expr :=
  (normalize? E f.rename a.expression).get (a.normalizationPresent f)

theorem Accepted.normalized_spec (a : Accepted E) (f : NameMap E F) :
    normalize? E f.rename a.expression = some (a.normalizedExpression f) ∧
    decodeFormula? F (a.normalizedExpression f) = some (Uflia.Term.map f.abstract a.formula) := by
  obtain ⟨output, hn, hd⟩ := normalizeFormula_success f a.expression a.formula a.decoded
  have heq : a.normalizedExpression f = output :=
    Option.get_of_eq_some (a.normalizationPresent f) hn
  rw [heq]
  exact ⟨hn, hd⟩

/-- Rename an actual accepted byte representative by normalizing its source
expression, rendering the result, and proving both actual executable boundaries. -/
def Accepted.map (a : Accepted E) (f : NameMap E F) : Accepted F where
  bytes := Writer.render (a.normalizedExpression f)
  expression := a.normalizedExpression f
  formula := Uflia.Term.map f.abstract a.formula
  read := Writer.read_render _ (normalize_legal f a.expression _ a.legal (a.normalized_spec f).1)
  decoded := (a.normalized_spec f).2

/-- Sentence action is induced on the actual representative quotient by decoded
formula commutation. Identity may eliminate lets in representative bytes. -/
def Sentence.map (f : NameMap E F) : Sentence E → Sentence F :=
  Quotient.map (fun a => a.map f) (by
    intro a b h
    change Uflia.Term.map f.abstract a.formula = Uflia.Term.map f.abstract b.formula
    exact congrArg (Uflia.Term.map f.abstract) h)

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
