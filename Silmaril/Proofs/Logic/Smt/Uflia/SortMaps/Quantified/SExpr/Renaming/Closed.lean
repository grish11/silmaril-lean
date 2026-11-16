module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Scoped.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Fuel.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory
open Uflia.SExpr (Environment Expr expressionFuel)
open Uflia.Quantified.SExpr
variable {E F : Environment}

/-- Context equality acts on the actual scoped decoder, without a semantic assumption. -/
theorem decodeScopedFuel_cast (fuel : Nat) {k : Nat}
    {Γ Δ : Fin k → SortCode String} (h : Γ = Δ) (locals : Locals F Γ) (expression : Expr) :
    decodeScopedFuel? F fuel (castLocals h locals) expression =
      (decodeScopedFuel? F fuel locals expression).map (castPacked h) := by
  cases h
  have packedId : castPacked (E := F) (rfl : Γ = Γ) = id := by
    funext value
    cases value
    rfl
  have localsId : castLocals (rfl : Γ = Γ) locals = locals := by
    calc
      castLocals (rfl : Γ = Γ) locals = locals.map id := by
        apply List.map_congr_left
        intro entry _
        rw [packedId]
        cases entry
        rfl
      _ = locals := List.map_id locals
  rw [localsId, packedId]
  exact (congrFun Option.map_id _).symm

/-- The closed entry returns the actual rewritten syntax at its own decoder
budget. The explicit cast only identifies two empty dependent contexts. -/
theorem renameTerm_success (f : NameMap E F) (expression : Expr)
    (value : PackedTerm E (fun i : Fin 0 => i.elim0))
    (decoded : decodeTerm? E expression = some value) :
    ∃ output, rename? f expression = some output ∧
      decodeTerm? F output = some
        (castPacked (Hom.sorts_empty f.abstract) (mapPacked f.abstract value)) := by
  obtain ⟨output, renamed, mapped⟩ := renameScoped_success f (expressionFuel expression)
    [] (firstFresh F) (by simp [ValidScope]) (Nat.le_refl _) expression value decoded
  refine ⟨output, renamed, ?_⟩
  change decodeScopedFuel? F (expressionFuel output) [] output = _
  rw [rename_fuel f expression output renamed]
  have casted := decodeScopedFuel_cast (expressionFuel expression)
    (Hom.sorts_empty f.abstract) (targetLocals f.abstract []) output
  rw [mapped, Option.map_some] at casted
  exact casted

/-- Full accepted source grammar transports to the exact abstract varying-sort
sentence, including quantified terms in Boolean expression positions. -/
theorem renameSentence_success (f : NameMap E F) (expression : Expr)
    (sentence : Uflia.Quantified.Sentence E.signature)
    (decoded : decodeSentence? E expression = some sentence) :
    ∃ output, rename? f expression = some output ∧
      decodeSentence? F output = some (Hom.quantifiedSentence f.abstract sentence) := by
  change (decodeTerm? E expression).bind _ = some sentence at decoded
  obtain ⟨value, source, typed⟩ := Option.bind_eq_some_iff.mp decoded
  obtain ⟨output, renamed, mapped⟩ := renameTerm_success f expression value source
  refine ⟨output, renamed, ?_⟩
  change (decodeTerm? F output).bind _ = _
  rw [mapped]
  change (castPacked (Hom.sorts_empty f.abstract) (mapPacked f.abstract value)).expect? .bool = _
  exact expect_heq (Hom.sorts_empty f.abstract) f.abstract.bool
    (mapPacked f.abstract value)
    (castPacked (Hom.sorts_empty f.abstract) (mapPacked f.abstract value))
    (castPacked_heq _ _).symm _ _ (cast_heq _ _).symm
    (expect_mapPacked_of_eq f.abstract value sentence typed)

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
