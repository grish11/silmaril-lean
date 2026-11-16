module

public import Silmaril.Logic.Smt.Uflia.SExpr.Surface.Thms
import Mathlib.Tactic.CasesM

-- The case analyses below run uniform tactic blocks over every constructor pair; the
-- unused-tactic linter flags the branches where a step happens to be a no-op.
set_option linter.unusedTactic false

/-! Unconditional packed source-value uniqueness over arbitrary semantic scopes.
The mutual induction reconciles binary/fold and binary/chain overlaps without
changing the source rules. Accepted scoped terms and formulas consequently have
exact source/decoded value and satisfaction equivalences. -/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.SExpr.Surface

open Silmaril.Logic.Algebraic

attribute [local instance] Classical.propDecidable

/-- A source expression has at most one packed sort/value result. -/
def Unique (E : Environment) (M : Packaged.GlobalModel) (scope : Scope M)
    (expression : Expr) : Prop :=
  ∀ (a b : Value M), Evaluates E M scope expression a.sort a.value →
    Evaluates E M scope expression b.sort b.value → a = b

/-- Packing values of a fixed sort is injective. -/
theorem value_mk_injective (M : Packaged.GlobalModel) (sort : SortCode String) :
    Function.Injective (Value.mk sort : M.carriers.value sort → Value M) := by
  intro a b equal
  simpa only [Value.mk.injEq, heq_eq_eq, true_and] using equal

private theorem natural_true_none : naturalNumeral? "true" = none := rfl
private theorem natural_false_none : naturalNumeral? "false" = none := rfl
attribute [local simp] natural_true_none natural_false_none

/-- Atom dispatch has a unique result, even for arbitrary semantic locals. -/
theorem atom_unique (E : Environment) (M : Packaged.GlobalModel) (scope : Scope M)
    (name : String) : Unique E M scope (.atom name) := by
  intro a b left right
  rcases a with ⟨sa, va⟩
  rcases b with ⟨sb, vb⟩
  dsimp only at left right ⊢
  generalize expressionEq : (.atom name : Expr) = expression at right
  cases left with
  | boolean b =>
    cases b <;> cases right with
    | boolean b => cases b <;> simp_all
    | _ =>
      simp_all
      all_goals subst_vars
      all_goals simp_all [reserved]
  | numeral =>
    cases right with
    | boolean b => cases b <;> simp_all
    | _ => simp_all
  | «local» =>
    cases right with
    | boolean b => cases b <;> simp_all
    | _ =>
      simp_all
      all_goals subst_vars
      all_goals rfl
  | constant =>
    cases right with
    | boolean b => cases b <;> simp_all [reserved]
    | _ =>
      simp_all
      all_goals subst_vars
      all_goals apply heq_of_eq
      all_goals congr 1
      all_goals funext j
      all_goals have impossible := j.isLt
      all_goals simp_all

/-- Lists of homogeneous values can be recovered from their packed values. -/
theorem packed_values_injective (M : Packaged.GlobalModel) (sort : SortCode String) :
    Function.Injective (List.map (Value.mk sort : M.carriers.value sort → Value M)) := by
  intro xs ys same
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at same
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at same
      have head := value_mk_injective M sort same.1
      cases head
      exact congrArg (List.cons x) (ih same.2)

/-- A nonempty packed operand family also identifies its homogeneous sort. -/
theorem packed_values_nonempty {M : Packaged.GlobalModel} {a b : SortCode String}
    (xs : List (M.carriers.value a)) (ys : List (M.carriers.value b))
    (nonempty : xs ≠ [])
    (same : xs.map (Value.mk a) = ys.map (Value.mk b)) :
    ∃ sortEq : a = b, sortEq ▸ xs = ys := by
  cases xs with
  | nil => exact (nonempty rfl).elim
  | cons x xs =>
    cases ys with
    | nil => simp at same
    | cons y ys =>
      have sortEq : a = b := congrArg Value.sort (List.cons.inj same).1
      cases sortEq
      exact ⟨rfl, packed_values_injective M a same⟩


attribute [local simp] Unary.token Binary.token FoldOp.token CompareOp.token reserved
attribute [local simp] Unary.value Binary.value FoldOp.value CompareOp.value

set_option maxHeartbeats 400000 in
/-- Every semantic derivation has the unique packed source value. -/
theorem evaluates_value_unique {E : Environment} {M : Packaged.GlobalModel}
    {scope : Scope M} {expression : Expr} {sort : SortCode String}
    {value : M.carriers.value sort} (derivation : Evaluates E M scope expression sort value) :
    ∀ otherSort (otherValue : M.carriers.value otherSort),
      Evaluates E M scope expression otherSort otherValue →
      (⟨sort, value⟩ : Value M) = ⟨otherSort, otherValue⟩ := by
  refine Evaluates.rec
    (motive_1 := fun scope expression sort value _ =>
      ∀ otherSort (otherValue : M.carriers.value otherSort),
        Evaluates E M scope expression otherSort otherValue →
        (⟨sort, value⟩ : Value M) = ⟨otherSort, otherValue⟩)
    (motive_2 := fun scope inputs es args _ =>
      ∀ other, ArgumentsEvaluate E M scope inputs es other → args = other)
    (motive_3 := fun scope sort es values _ =>
      ∀ otherSort otherValues, OperandsEvaluate E M scope otherSort es otherValues →
        values.map (Value.mk sort) = otherValues.map (Value.mk otherSort))
    (motive_4 := fun scope bindings values _ =>
      ∀ otherValues, BindingsEvaluate E M scope bindings otherValues → values = otherValues)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ derivation
  · intro scope b t w right
    exact atom_unique E M scope _ _ _ (.boolean b) right
  · intro scope text n parsed unbound t w right
    exact atom_unique E M scope _ _ _ (.numeral text n parsed unbound) right
  · intro scope name value notTrue notFalse found t w right
    exact atom_unique E M scope _ _ _ (.local name value notTrue notFalse found) right
  · intro scope name i unreserved unbound notNumeral found empty args t w right
    exact atom_unique E M scope _ _ _
      (.constant name i unreserved unbound notNumeral found empty args) right
  · intro scope name i unreserved unbound found es nonempty args evaluated ih t w right
    generalize sourceEq : (.list (.atom name :: es) : Expr) = source at right
    cases right with
    | app otherName otherIndex otherUnreserved otherUnbound otherFound otherEs otherNonempty otherArgs otherEval =>
      simp only [SE.list.injEq, List.cons.injEq, SE.atom.injEq] at sourceEq
      rcases sourceEq with ⟨nameEq, argsEq⟩
      cases nameEq
      cases argsEq
      have indexEq := Option.some.inj (found.symm.trans otherFound)
      cases indexEq
      have same := ih otherArgs otherEval
      cases same
      rfl
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope input output op e v operand ih t w right
    generalize sourceEq : (.list [.atom op.token, e] : Expr) = source at right
    cases right with
    | unary otherOp otherOperand =>
      cases op <;> cases otherOp <;> simp at sourceEq
      all_goals subst_vars
      all_goals have same := value_mk_injective M _ (ih _ _ otherOperand)
      all_goals cases same
      all_goals rfl
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope input output op a b x y left right ihLeft ihRight t w other
    generalize sourceEq : (.list [.atom op.token, a, b] : Expr) = source at other
    cases other with
    | binary otherOp otherLeft otherRight =>
      cases op <;> cases otherOp <;> simp at sourceEq
      all_goals rcases sourceEq with ⟨rfl, rfl⟩
      all_goals have xSame := value_mk_injective M _ (ihLeft _ _ otherLeft)
      all_goals have ySame := value_mk_injective M _ (ihRight _ _ otherRight)
      all_goals cases xSame
      all_goals cases ySame
      all_goals rfl
    | fold otherOp otherA otherB otherRest otherX otherXs otherFirst otherRemaining =>
      cases op <;> cases otherOp <;> simp at sourceEq
      all_goals rcases sourceEq with ⟨rfl, rfl, rfl⟩
      all_goals cases otherRemaining with
      | cons otherRight otherNil =>
        cases otherNil
        have xSame := value_mk_injective M _ (ihLeft _ _ otherFirst)
        have ySame := value_mk_injective M _ (ihRight _ _ otherRight)
        cases xSame
        cases ySame
        rfl
    | comparison otherOp otherA otherB otherRest otherValues otherOperands =>
      cases op <;> cases otherOp <;> simp at sourceEq
      all_goals rcases sourceEq with ⟨rfl, rfl, rfl⟩
      all_goals cases otherOperands with
      | cons otherLeft otherTail =>
        cases otherTail with
        | cons otherRight otherNil =>
          cases otherNil
          have xSame := value_mk_injective M _ (ihLeft _ _ otherLeft)
          have ySame := value_mk_injective M _ (ihRight _ _ otherRight)
          cases xSame
          cases ySame
          simp [adjacentValue]
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope sort op a b rest x xs first remaining ihFirst ihRemaining t w other
    generalize sourceEq : (.list (.atom op.token :: a :: b :: rest) : Expr) = source at other
    cases other with
    | fold otherOp otherA otherB otherRest otherX otherXs otherFirst otherRemaining =>
      cases op <;> cases otherOp <;> simp at sourceEq
      all_goals rcases sourceEq with ⟨rfl, rfl, rfl⟩
      all_goals have firstSame := value_mk_injective M _ (ihFirst _ _ otherFirst)
      all_goals have restSame := packed_values_injective M _ (ihRemaining _ _ otherRemaining)
      all_goals cases firstSame
      all_goals cases restSame
      all_goals rfl
    | binary otherOp otherLeft otherRight =>
      cases op <;> cases otherOp <;> simp at sourceEq
      all_goals rcases sourceEq with ⟨rfl, rfl, rfl⟩
      all_goals have firstSame := value_mk_injective M _ (ihFirst _ _ otherLeft)
      all_goals have restSame := packed_values_injective M _ (ihRemaining _ _ (.cons otherRight (.nil scope _)))
      all_goals cases firstSame
      all_goals cases restSame
      all_goals rfl
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope a b rest values operands ih t w other
    generalize sourceEq : (.list (.atom "*" :: a :: b :: rest) : Expr) = source at other
    cases other with
    | multiply otherA otherB otherRest otherValues otherOperands =>
      simp at sourceEq
      rcases sourceEq with ⟨rfl, rfl, rfl⟩
      have same := packed_values_injective M .int (ih _ _ otherOperands)
      cases same
      rfl
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope op a b rest values operands ih t w other
    generalize sourceEq : (.list (.atom op.token :: a :: b :: rest) : Expr) = source at other
    cases other with
    | comparison otherOp otherA otherB otherRest otherValues otherOperands =>
      cases op <;> cases otherOp <;> simp at sourceEq
      all_goals rcases sourceEq with ⟨rfl, rfl, rfl⟩
      all_goals have same := packed_values_injective M .int (ih _ _ otherOperands)
      all_goals cases same
      all_goals rfl
    | binary otherOp otherLeft otherRight =>
      cases op <;> cases otherOp <;> simp at sourceEq
      all_goals rcases sourceEq with ⟨rfl, rfl, rfl⟩
      all_goals have same := packed_values_injective M .int (ih _ _ (.cons otherLeft (.cons otherRight (.nil scope .int))))
      all_goals cases same
      all_goals simp [adjacentValue]
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope sort a b rest values operands ih t w other
    generalize sourceEq : (.list (.atom "=" :: a :: b :: rest) : Expr) = source at other
    have nonempty : values ≠ [] := by
      intro empty
      rw [empty] at operands
      cases operands
    cases other with
    | equalChain otherA otherB otherRest otherValues otherOperands =>
      simp at sourceEq
      rcases sourceEq with ⟨rfl, rfl, rfl⟩
      rcases packed_values_nonempty values otherValues nonempty (ih _ _ otherOperands) with
        ⟨sortEq, valuesEq⟩
      cases sortEq
      cases valuesEq
      rfl
    | equality otherLeft otherRight =>
      simp at sourceEq
      rcases sourceEq with ⟨rfl, rfl, rfl⟩
      rcases packed_values_nonempty values _ nonempty
          (ih _ _ (.cons otherLeft (.cons otherRight (.nil scope _)))) with
        ⟨sortEq, valuesEq⟩
      cases sortEq
      cases valuesEq
      simp [adjacentValue]
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope sort a b rest values operands ih t w other
    generalize sourceEq : (.list (.atom "distinct" :: a :: b :: rest) : Expr) = source at other
    cases other with
    | distinct otherA otherB otherRest otherValues otherOperands =>
      simp at sourceEq
      rcases sourceEq with ⟨rfl, rfl, rfl⟩
      have nonempty : values ≠ [] := by
        intro empty
        rw [empty] at operands
        cases operands
      rcases packed_values_nonempty values otherValues nonempty (ih _ _ otherOperands) with
        ⟨sortEq, valuesEq⟩
      cases sortEq
      cases valuesEq
      rfl
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope a b sort x y left right ihLeft ihRight t w other
    generalize sourceEq : (.list [.atom "=", a, b] : Expr) = source at other
    cases other with
    | equality otherLeft otherRight =>
      simp at sourceEq
      rcases sourceEq with ⟨rfl, rfl⟩
      have leftSame := ihLeft _ _ otherLeft
      have sortEq := congrArg Value.sort leftSame
      cases sortEq
      have xSame := value_mk_injective M _ leftSame
      have ySame := value_mk_injective M _ (ihRight _ _ otherRight)
      cases xSame
      cases ySame
      rfl
    | equalChain otherA otherB otherRest otherValues otherOperands =>
      simp at sourceEq
      rcases sourceEq with ⟨rfl, rfl, rfl⟩
      cases otherOperands with
      | cons otherLeft otherTail =>
        cases otherTail with
        | cons otherRight otherNil =>
          cases otherNil
          have leftSame := ihLeft _ _ otherLeft
          have sortEq := congrArg Value.sort leftSame
          cases sortEq
          have xSame := value_mk_injective M _ leftSame
          have ySame := value_mk_injective M _ (ihRight _ _ otherRight)
          cases xSame
          cases ySame
          simp [adjacentValue]
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope c a b sort condition x y test left right ihTest ihLeft ihRight t w other
    generalize sourceEq : (.list [.atom "ite", c, a, b] : Expr) = source at other
    cases other with
    | ite otherTest otherLeft otherRight =>
      simp at sourceEq
      rcases sourceEq with ⟨rfl, rfl, rfl⟩
      have testSame := value_mk_injective M .bool (ihTest _ _ otherTest)
      have leftSame := ihLeft _ _ otherLeft
      have sameSort := congrArg Value.sort leftSame
      cases sameSort
      have leftValueSame := value_mk_injective M _ leftSame
      have rightValueSame := value_mk_injective M _ (ihRight _ _ otherRight)
      cases testSame
      cases leftValueSame
      cases rightValueSame
      rfl
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope values bindings body sort value nonempty bindingsValue bodyValue ihBindings ihBody t w other
    generalize sourceEq : (.list [.atom "let", .list bindings, body] : Expr) = source at other
    cases other with
    | letExpr otherNonempty otherBindings otherBody =>
      simp at sourceEq
      rcases sourceEq with ⟨rfl, rfl⟩
      have sameBindings := ihBindings _ otherBindings
      cases sameBindings
      exact ihBody _ _ otherBody
    | _ =>
      all_goals try (simp at sourceEq)
      all_goals try (cases_type* Unary Binary FoldOp CompareOp)
      all_goals simp_all
  · intro scope other proof
    cases proof
    rfl
  · intro scope input inputs e es x xs head tail ihHead ihTail other proof
    cases proof with
    | cons y ys otherHead otherTail =>
      have same := value_mk_injective M input (ihHead _ _ otherHead)
      have tailSame := ihTail _ otherTail
      cases same
      cases tailSame
      rfl
  · intro scope sort otherSort otherValues proof
    cases proof
    rfl
  · intro scope sort e value es values head tail ihHead ihTail otherSort otherValues proof
    cases proof with
    | cons otherHead otherTail =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨ihHead _ _ otherHead, ihTail _ _ otherTail⟩
  · intro scope otherValues proof
    cases proof
    rfl
  · intro scope values rest e name value legal unreserved fresh rhs tail ihHead ihTail otherValues proof
    cases proof with
    | cons name otherValue otherLegal otherUnreserved otherFresh otherRhs otherTail =>
      have same : value = otherValue := ihHead _ _ otherRhs
      have tailSame := ihTail _ otherTail
      cases same
      cases tailSame
      rfl

/-- The direct relation is functional in its packed sort/value result. -/
theorem evaluates_unique (E : Environment) (M : Packaged.GlobalModel)
    (scope : Scope M) (expression : Expr) : Unique E M scope expression := by
  intro a b left right
  exact evaluates_value_unique left b.sort b.value right

/-- On every accepted scoped term, direct source evaluation is exactly its denotation. -/
theorem evaluates_iff_decoded {E : Environment} (M : Packaged.GlobalModel)
    (fuel : Nat) (locals : Locals E) (expression : Expr) (term : PackedTerm E)
    (decoded : decodeScopedFuel? E fuel locals expression = some term) (value : Value M) :
    Evaluates E M (interpretLocals M locals) expression value.sort value.value ↔
      value = interpretTerm M term := by
  have forward := decodeScopedFuel_preserves M fuel locals expression term decoded
  constructor
  · intro direct
    exact evaluates_value_unique direct term.sort _ forward
  · intro same
    cases same
    exact forward

/-- Public term acceptance gives an exact source-value correspondence. -/
theorem evaluates_iff_decodeTerm {E : Environment} (M : Packaged.GlobalModel)
    (expression : Expr) (term : PackedTerm E)
    (decoded : decodeTerm? E expression = some term) (value : Value M) :
    Evaluates E M [] expression value.sort value.value ↔ value = interpretTerm M term :=
  evaluates_iff_decoded M (expressionFuel expression) [] expression term decoded value

/-- Accepted formulas have equivalent direct and decoded truth. -/
theorem holds_iff_decodeFormula {E : Environment} (M : Packaged.GlobalModel)
    (expression : Expr) (formula : Formula E.signature)
    (decoded : decodeFormula? E expression = some formula) :
    Holds E M expression ↔ (M.reduct (Packaged.nameMap E)).Holds formula := by
  constructor
  · intro direct
    have same := value_mk_injective M .bool
      (evaluates_value_unique direct .bool _ (decodeFormula_preserves M expression formula decoded))
    change (M.reduct (Packaged.nameMap E)).eval formula = true
    exact same.symm
  · intro truth
    exact expressionHolds_implies M expression ⟨formula, decoded, truth⟩

/-- Each accepted assertion has direct source truth exactly when its old presentation holds. -/
theorem assertion_direct_iff {E : Environment} (M : Packaged.GlobalModel) (a : Assertion E) :
    Holds E M a.expression ↔ ExpressionHolds E a.expression (M.reduct (Packaged.nameMap E)) :=
  (holds_iff_decodeFormula M a.expression a.formula a.decoded).trans
    (expressionHolds_iff a (M.reduct (Packaged.nameMap E))).symm

/-- The whole accepted assertion list has exact direct/decoded satisfaction in one model. -/
theorem assertions_direct_iff {E : Environment} (M : Packaged.GlobalModel)
    (assertions : List (Assertion E)) :
    (∀ a ∈ assertions, Holds E M a.expression) ↔
      AssertionsHolds assertions (M.reduct (Packaged.nameMap E)) := by
  constructor
  · intro direct a member
    exact (assertion_direct_iff M a).mp (direct a member)
  · intro decoded a member
    exact (assertion_direct_iff M a).mpr (decoded a member)

end Silmaril.Logic.Smt.Uflia.SExpr.Surface
