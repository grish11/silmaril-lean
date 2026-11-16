module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.ContextConversion.Thms
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityLambdaCongruence

public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
open Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Lambda congruence with independently checked equality of annotations and bodies.
The codomain and body premises are checked in the original domain context. -/
theorem Equality.lamCongr {k n : ℕ} {S : Context k} {Γ : Context n}
    {A A' : Term n} {B b b' : Term (n + 1)} {s : LFSort}
    (hAA' : Equality S Γ A A' (.univ 0))
    (hB : Equality S (Γ.snoc A) B B (.univ s.val))
    (hb : Equality S (Γ.snoc A) b b' B) :
    Equality S Γ (.lam A b) (.lam A' b') (.pi A B) :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityLambdaCongruence.lambda_congr hAA' hB hb

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality
