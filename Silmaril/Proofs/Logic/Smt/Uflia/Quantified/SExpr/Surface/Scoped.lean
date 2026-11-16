module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Surface.Quantifiers

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
open Silmaril.Logic.Smt.Uflia.SExpr
variable {E : Environment} (M : Model E.signature)

/-- Scoped correspondence includes rejection, arbitrary assignments and all
source Boolean positions. Let RHSs share the old scope. -/
theorem evaluateScopedFuel_eq (fuel : Nat) {k : Nat} {Γ : Fin k → SortCode String}
    (locals : SExpr.Locals E Γ) (ρ : ∀ i, M.carriers.value (Γ i)) (e : Expr) :
    evaluateScopedFuel? E M fuel (denoteLocals M ρ locals) e =
      (SExpr.decodeScopedFuel? E fuel locals e).map (denote M ρ) := by
  induction fuel generalizing k Γ locals e with
  | zero => rfl
  | succ fuel ih =>
    have recur : evaluateScopedFuel? E M fuel (denoteLocals M ρ locals) =
        fun child => (SExpr.decodeScopedFuel? E fuel locals child).map (denote M ρ) :=
      funext (ih locals ρ)
    have quant (universal : Bool) (bs : List (String × SortCode String)) (body : Expr) :=
      quantify_commute M universal (evaluateScopedFuel? E M fuel)
        (fun ls child => SExpr.decodeScopedFuel? E fuel ls child)
        (fun ls assignment child => ih ls assignment child) locals ρ bs body
    have letBody (values : SExpr.Locals E Γ) (body : Expr) :
        evaluateScopedFuel? E M fuel (denoteLocals M ρ values ++ denoteLocals M ρ locals) body =
          (SExpr.decodeScopedFuel? E fuel (values ++ locals) body).map (denote M ρ) := by
      simpa only [denoteLocals_append] using ih (values ++ locals) ρ body
    have atom_case (name : String) :
        (match (SExpr.local? locals name).map (denote M ρ) with
        | some value => some value
        | none => match numeral? (.atom name) with
          | some n => some (integer M n)
          | none => (SExpr.applyUF? E (SExpr.decodeScopedFuel? E fuel locals) name []).map (denote M ρ)) =
        (match SExpr.local? locals name with
        | some term => some term
        | none => match numeral? (.atom name) with
          | some n => some (⟨.int, Quantified.Term.integer n⟩ : SExpr.PackedTerm E Γ)
          | none => SExpr.applyUF? E (SExpr.decodeScopedFuel? E fuel locals) name []).map (denote M ρ) := by
      cases SExpr.local? locals name with
      | some term => rfl
      | none => cases numeral? (.atom name) <;> rfl
    simp only [evaluateScopedFuel?, SExpr.decodeScopedFuel?]
    split <;> simp_all [uf_commute, unary_commute, implication_commute,
      xor_commute, ite_commute, fold_commute, compare_commute, equalities_commute,
      multiply_commute, local_commute, letBindings_commute,
      Option.bind_map, Option.map_bind] <;>
      first
      | exact atom_case _
      | rfl
      | (split <;> simp_all)

/-- Closed evaluation is exactly the semantic image of decoding, including failure. -/
theorem evaluate_eq (e : Expr) :
    evaluate? E M e = (SExpr.decodeTerm? E e).map
      (denote M (fun i : Fin 0 => i.elim0)) :=
  evaluateScopedFuel_eq M (expressionFuel e) [] (fun i : Fin 0 => i.elim0) e

/-- The independent source truth agrees with typed truth after Boolean admission. -/
theorem holds_iff_of_decoded {e : Expr} {sentence : Sentence E.signature}
    (decoded : SExpr.decodeSentence? E e = some sentence) :
    Holds E M e ↔ Sentence.Holds sentence M := by
  unfold SExpr.decodeSentence? at decoded
  cases ht : SExpr.decodeTerm? E e with
  | none => simp [ht] at decoded
  | some packed =>
    rw [ht] at decoded
    change packed.expect? .bool = some sentence at decoded
    rcases packed with ⟨sort, term⟩
    unfold SExpr.PackedTerm.expect? at decoded
    split at decoded
    next same =>
      change sort = .bool at same
      subst sort
      cases decoded
      simp [Holds, evaluate_eq, ht, denote, denoteData, Sentence.Holds, Formula.Holds]
    next => simp at decoded

theorem accepted_holds_iff (a : SExpr.ByteAccepted E) :
    Holds E M a.expression ↔ a.Holds M := holds_iff_of_decoded M a.decoded

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
