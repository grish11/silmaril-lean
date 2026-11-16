module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete.Action.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
open CategoryTheory Silmaril.Logic.Algebraic
variable {E F G : Environment}

@[simp] theorem Accepted.map_formula (a : Accepted E) (f : NameMap E F) :
    (a.map f).formula = Uflia.Term.map f.abstract a.formula := rfl

@[simp] theorem Accepted.map_expression (a : Accepted E) (f : NameMap E F) :
    (a.map f).expression = a.normalizedExpression f := rfl

@[simp] theorem Accepted.map_bytes (a : Accepted E) (f : NameMap E F) :
    (a.map f).bytes = Silmaril.Logic.Smt.SExpr.Writer.render (a.normalizedExpression f) := rfl

@[simp] theorem Sentence.map_mk (f : NameMap E F) (a : Accepted E) :
    Sentence.map f (Sentence.mk a) = Sentence.mk (a.map f) := rfl

/-- Actual decoding is natural for the concrete quotient sentence action. -/
@[simp] theorem Sentence.decode_map (f : NameMap E F) (s : Sentence E) :
    (Sentence.map f s).decode = Uflia.Term.map f.abstract s.decode := by
  refine Quotient.inductionOn s ?_
  intro a
  rfl

/-- Identity is a decoded-quotient law, with no claim of literal byte identity. -/
theorem Sentence.map_id (s : Sentence E) : Sentence.map (NameMap.id E) s = s := by
  apply (Sentence.decode_eq_iff _ _).mp
  rw [Sentence.decode_map]
  exact Uflia.Term.map_id s.decode

/-- Composition preserves the computed formula even though normalization may
choose different literal representatives at intermediate stages. -/
theorem Sentence.map_comp (f : NameMap E F) (g : NameMap F G) (s : Sentence E) :
    Sentence.map (f.comp g) s = Sentence.map g (Sentence.map f s) := by
  apply (Sentence.decode_eq_iff _ _).mp
  rw [Sentence.decode_map, Sentence.decode_map, Sentence.decode_map]
  exact Uflia.Term.map_comp f.abstract g.abstract s.decode

/-- Model reducts and concrete sentence normalization satisfy the institution
condition for arbitrary maps, including symbol identifications. -/
theorem holds_map (f : NameMap E F) (M : Uflia.Model F.signature) (s : Sentence E) :
    Holds M (Sentence.map f s) ↔ Holds (Uflia.Model.reduct f.abstract M) s := by
  change M.Holds (Sentence.map f s).decode ↔ (Uflia.Model.reduct f.abstract M).Holds s.decode
  rw [Sentence.decode_map]
  exact Uflia.Model.holds_map f.abstract M s.decode

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Concrete
