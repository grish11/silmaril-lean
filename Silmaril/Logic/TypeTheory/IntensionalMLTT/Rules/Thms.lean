module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Rules.Defs

@[expose] public section

/-! Concrete derivations exercise binders, identity introduction and J computation. -/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- The closed identity function on natural numbers. -/
def natIdentity : Term 0 := .lam .nat (.var 0)

/-- An explicit derivation tree, with its domain and codomain formation proofs. -/
def natIdentity_derivation : Derivation .nil natIdentity (.pi .nat .nat) := by
  have hNat : Derivation .nil .nat (.univ 0) := .nat .nil
  have hΓ : ContextDerivation (Context.nil.snoc .nat) := .snoc .nil hNat
  exact .lam hNat (.nat hΓ) (.var hΓ .here)

/-- Beta computation is intensional conversion, without reflection. -/
theorem natIdentity_zero : Convertible (.app natIdentity .zero) .zero :=
  ⟨.beta .nat (.var 0) .zero⟩

/-- A step function that increments the recursive result, ignoring its predecessor. -/
def natIncrementStep : Term 0 := .lam .nat (.lam .nat (.succ (.var 0)))

/-- Both step-function arguments and the innermost recursive result are checked. -/
def natIncrementStep_derivation :
    Derivation .nil natIncrementStep (.pi .nat (.pi .nat .nat)) := by
  have hNat : Derivation .nil .nat (.univ 0) := .nat .nil
  have hΓ : ContextDerivation (Context.nil.snoc .nat) := .snoc .nil hNat
  have hΔ : ContextDerivation ((Context.nil.snoc .nat).snoc .nat) := .snoc hΓ (.nat hΓ)
  exact .lam hNat (.pi (.nat hΓ) (.nat hΔ))
    (.lam (.nat hΓ) (.nat hΔ) (.succ (.var hΔ .here)))

/-- A concrete dependent-recursion term at the numeral one. -/
def natRecOne : Term 0 := .natrec .nat .zero natIncrementStep (.succ .zero)

/-- The ordinary two-argument step type checks against the declared recursor rule. -/
def natRecOne_derivation : Derivation .nil natRecOne .nat := by
  have hΓ : ContextDerivation (Context.nil.snoc .nat) := .snoc .nil (.nat .nil)
  exact .natrec (.nat hΓ) (.zero .nil) natIncrementStep_derivation (.succ (.zero .nil))

/-- Computation uses the recursive result as the step function's second argument. -/
theorem natRecOne_beta : TypedEq .nil natRecOne (.succ .zero) .nat := by
  refine ⟨⟨natRecOne_derivation⟩, ⟨.succ (.zero .nil)⟩, ⟨?_⟩⟩
  apply Conversion.trans (.nat_succ .nat .zero natIncrementStep .zero)
  apply Conversion.trans
    (.congr_app (.beta .nat (.lam .nat (.succ (.var 0))) .zero)
      (.nat_zero .nat .zero natIncrementStep))
  exact .beta .nat (.succ (.var 0)) .zero

/-- Based path induction with the constant natural-number motive. -/
def jZero : Term 0 := .j .nat .zero .nat .zero .zero (.refl .zero)

/-- The J example checks the endpoint/path order in the two-binder motive. -/
def jZero_derivation : Derivation .nil jZero .nat := by
  have hNat : Derivation .nil .nat (.univ 0) := .nat .nil
  have hZero : Derivation .nil .zero .nat := .zero .nil
  have hΓ : ContextDerivation (Context.nil.snoc .nat) := .snoc .nil hNat
  have hId : Derivation (Context.nil.snoc .nat) (.id .nat .zero (.var 0)) (.univ 0) :=
    .id (.nat hΓ) (.zero hΓ) (.var hΓ .here)
  have hMotive : ContextDerivation (motiveContext .nil .nat .zero) := .snoc hΓ hId
  exact .j hNat hZero (.nat hMotive) hZero hZero (.refl hNat hZero)

/-- The checked J expression is judgmentally equal to its base case. -/
theorem jZero_beta : TypedEq .nil jZero .zero .nat :=
  ⟨⟨jZero_derivation⟩, ⟨.zero .nil⟩, ⟨.j_refl .nat .zero .nat .zero⟩⟩

end Silmaril.Logic.TypeTheory.IntensionalMLTT
