module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Scoped
public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Fuel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment}

/-- Default closed term decoding commutes with actual executable renaming.
Scope validity and freshness are discharged internally at the empty scope. -/
theorem renameTerm_success (f : NameMap E F) (expression : Expr)
    (value : PackedTerm E (fun i : Fin 0 => i.elim0))
    (decoded : decodeTerm? E expression = some value) :
    ∃ output, rename? f expression = some output ∧
      decodeTerm? F output = some (mapPacked f.abstract value) := by
  obtain ⟨output, renamed, mapped⟩ := renameScoped_success f (expressionFuel expression)
    [] (firstFresh F) (by simp [ValidScope]) (Nat.le_refl _) expression value decoded
  refine ⟨output, renamed, ?_⟩
  change decodeScopedFuel? F (expressionFuel output) [] output = _
  rw [rename_fuel f expression output renamed]
  exact mapped

/-- Every admitted Boolean expression produces an actual renamed expression
with exactly the mapped typed sentence, using both default decoder entries. -/
theorem renameSentence_success (f : NameMap E F) (expression : Expr)
    (sentence : Quantified.Sentence E.signature)
    (decoded : decodeSentence? E expression = some sentence) :
    ∃ output, rename? f expression = some output ∧
      decodeSentence? F output = some (sentence.map f.abstract) := by
  change (decodeTerm? E expression).bind _ = some sentence at decoded
  obtain ⟨value, source, typed⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨output, renamed, mapped⟩ := renameTerm_success f expression value source
  refine ⟨output, renamed, ?_⟩
  change (decodeTerm? F output).bind _ = _
  rw [mapped]
  change (mapPacked f.abstract value).expect? .bool = _
  rw [expect_map, typed]
  rfl

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
