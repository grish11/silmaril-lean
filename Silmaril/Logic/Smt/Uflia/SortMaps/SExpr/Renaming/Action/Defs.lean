module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Normalization.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Legality.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open CategoryTheory Uflia.SExpr
variable {E F G : Environment}

abbrev Accepted := Uflia.SExpr.Renaming.Concrete.Accepted
abbrev Sentence := Uflia.SExpr.Renaming.Concrete.Sentence

theorem normalizationPresent (f : NameMap E F) (a : Accepted E) :
    (Uflia.SExpr.Renaming.normalize? E f.rename a.expression).isSome := by
  obtain ⟨output, hn, _⟩ := normalizeFormula_success f a.expression a.formula a.decoded
  simp only [hn, Option.isSome_some]

/-- Extract the actual executable output; the proof only erases a precondition. -/
def normalizedExpression (f : NameMap E F) (a : Accepted E) : Expr :=
  (Uflia.SExpr.Renaming.normalize? E f.rename a.expression).get (normalizationPresent f a)

theorem normalized_spec (f : NameMap E F) (a : Accepted E) :
    Uflia.SExpr.Renaming.normalize? E f.rename a.expression = some (normalizedExpression f a) ∧
    decodeFormula? F (normalizedExpression f a) = some (Hom.formula f.abstract a.formula) := by
  obtain ⟨output, hn, hd⟩ := normalizeFormula_success f a.expression a.formula a.decoded
  have same : normalizedExpression f a = output :=
    Option.get_of_eq_some (normalizationPresent f a) hn
  rw [same]
  exact ⟨hn, hd⟩

/-- Reuse accepted-byte representatives, with newly rendered target bytes and
proved equalities at both the concrete reader and typed decoder boundaries. -/
def renameAccepted (f : NameMap E F) (a : Accepted E) : Accepted F where
  bytes := Silmaril.Logic.Smt.SExpr.Writer.render (normalizedExpression f a)
  expression := normalizedExpression f a
  formula := Hom.formula f.abstract a.formula
  read := Silmaril.Logic.Smt.SExpr.Writer.read_render _
    (normalize_legal f a.expression _ a.legal (normalized_spec f a).1)
  decoded := (normalized_spec f a).2

def mapSentence (f : NameMap E F) : Sentence E → Sentence F :=
  Quotient.map (renameAccepted f) (by
    intro a b h
    exact congrArg (Hom.formula f.abstract) h)

@[simp] theorem decode_map (f : NameMap E F) (s : Sentence E) :
    (mapSentence f s).decode = Hom.formula f.abstract s.decode := by
  refine Quotient.inductionOn s ?_
  intro a
  rfl

end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
