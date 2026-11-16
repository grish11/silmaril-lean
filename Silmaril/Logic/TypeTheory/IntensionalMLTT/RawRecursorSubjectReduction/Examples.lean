module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction.Thms
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Rules.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction.Examples

/-- A type-valued successor step returns the natural type. -/
def typeStep : Term 0 := .lam .nat (.lam (.univ 0) .nat)

def typeStep_derivation : Derivation .nil typeStep (.pi .nat (.pi (.univ 0) (.univ 0))) := by
  have hNat : Derivation .nil .nat (.univ 0) := .nat .nil
  have hΓ : ContextDerivation (Context.nil.snoc .nat) := .snoc .nil hNat
  have hU : Derivation (Context.nil.snoc .nat) (.univ 0) (.univ 1) := .univ hΓ 0
  have hΔ : ContextDerivation ((Context.nil.snoc .nat).snoc (.univ 0)) := .snoc hΓ hU
  exact .lam hNat (.pi hU (.univ hΔ 0)) (.lam hU (.univ hΔ 0) (.nat hΔ))

/-- This source typing genuinely ends in cumulativity, away from its motive's native carrier. -/
def cumulativeSource : Derivation .nil (.natrec (.univ 0) .nat typeStep .zero) (.univ 2) := by
  have hΓ : ContextDerivation (Context.nil.snoc .nat) := .snoc .nil (.nat .nil)
  have hNative : Derivation .nil (.natrec (.univ 0) .nat typeStep .zero) (.univ 0) :=
    .natrec (.univ hΓ 0) (.nat .nil) typeStep_derivation (.zero .nil)
  exact .cumulative hNative (by decide)

/-- The new theorem derives the contractum at the unchanged requested upper universe. -/
theorem cumulative_nat_zero :
    TypedEq .nil (.natrec (.univ 0) .nat typeStep .zero) .nat (.univ 2) :=
  TypedEq.nat_zero_of_typing ⟨cumulativeSource⟩

/-- An actual beta-redex carrier used to exercise the conversion ending. -/
def natAlias : Term 0 := .app (.lam .unit .nat) .star

def natAlias_derivation : Derivation .nil natAlias (.univ 0) := by
  have hUnit : Derivation .nil .unit (.univ 0) := .unit .nil
  have hΓ : ContextDerivation (Context.nil.snoc .unit) := .snoc .nil hUnit
  exact .app (.lam hUnit (.univ hΓ 0) (.nat hΓ)) (.star .nil)

/-- Successor computation retains a converted source type and its actual recursive call. -/
theorem converted_nat_successor :
    TypedEq .nil natRecOne
      (.app (.app natIncrementStep .zero) (.natrec .nat .zero natIncrementStep .zero)) natAlias := by
  have hSource : Derivation .nil natRecOne natAlias :=
    .conv natRecOne_derivation natAlias_derivation (.symm (.beta .unit .nat .star))
  exact TypedEq.nat_succ_of_typing ⟨hSource⟩

/-- Exact based-J contraction also retains a converted source carrier. -/
theorem converted_j_refl : TypedEq .nil jZero .zero natAlias := by
  have hSource : Derivation .nil jZero natAlias :=
    .conv jZero_derivation natAlias_derivation (.symm (.beta .unit .nat .star))
  exact TypedEq.j_refl_of_typing ⟨hSource⟩

end Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRecursorSubjectReduction.Examples
