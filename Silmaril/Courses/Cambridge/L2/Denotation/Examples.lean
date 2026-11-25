module

public import Silmaril.Courses.Cambridge.L2.Denotation.Adequacy

/-! # Ground observations of L2 closures -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.PureDenotation.Examples

/-- Slide 140. Apply a curried sum first to `3 + 4` and then to `5`. -/
def curriedSum : Expr :=
  (RawExpr.app (.app (.lam "x" .int (.lam "y" .int (.binary (.var "x") .add (.var "y"))))
    (.binary (.int 3) .add (.int 4))) (.int 5)).resolve []

def curriedSumTerm : Term [] curriedSum .int :=
  .app (.app (.lam (.lam (.add (.bvar rfl) (.bvar rfl)))) (.add (.int 3) (.int 4))) (.int 5)

theorem curriedSum_denotes : curriedSumTerm.denote .empty = 12 := by decide

theorem curriedSum_returns (s : Store) : Steps ⟨curriedSum, s⟩ ⟨.int 12, s⟩ :=
  ((curriedSumTerm.adequate .int s _).mpr (by rw [curriedSum_denotes]; rfl)).1

/-- Slide 140's higher-order application applies its function argument to `3`. -/
def higherOrder : Expr :=
  (RawExpr.app (.lam "f" (.arr .int .int) (.app (.var "f") (.int 3)))
    (.lam "x" .int (.binary (.binary (.int 1) .add (.int 2)) .add (.var "x")))).resolve []

def higherOrderTerm : Term [] higherOrder .int :=
  .app (.lam (.app (.bvar rfl) (.int 3))) (.lam (.add (.add (.int 1) (.int 2)) (.bvar rfl)))

theorem higherOrder_denotes : higherOrderTerm.denote .empty = 6 := by decide

theorem higherOrder_returns (s : Store) : Steps ⟨higherOrder, s⟩ ⟨.int 6, s⟩ :=
  ((higherOrderTerm.adequate .int s _).mpr (by rw [higherOrder_denotes]; rfl)).1

/-- The later binding of `x` leaves the saved environment of `f` intact. -/
def lexical : Expr :=
  (RawExpr.letE "x" .int (.int 7)
    (.letE "f" (.arr .int .int) (.lam "y" .int (.binary (.var "x") .add (.var "y")))
      (.letE "x" .int (.int 100) (.app (.var "f") (.int 5))))).resolve []

def lexicalTerm : Term [] lexical .int :=
  .letE (.int 7) (.letE (.lam (.add (.bvar rfl) (.bvar rfl)))
    (.letE (.int 100) (.app (.bvar rfl) (.int 5))))

theorem lexical_denotes : lexicalTerm.denote .empty = 12 := by decide

theorem lexical_returns (s : Store) : Steps ⟨lexical, s⟩ ⟨.int 12, s⟩ :=
  ((lexicalTerm.adequate .int s _).mpr (by rw [lexical_denotes]; rfl)).1

end Silmaril.Courses.Cambridge.L2.PureDenotation.Examples
