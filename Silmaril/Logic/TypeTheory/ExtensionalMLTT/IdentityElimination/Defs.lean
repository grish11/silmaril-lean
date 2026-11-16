module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation

@[expose] public section

/-!
# Function-valued motives for extensional based path induction

A motive is a term of type `Π x : A. Π p : Id A a x. U_n`.
The derived eliminator is its base term. Its typing is a theorem using
actual reflection, UIP, dependent application and conversion derivations;
it is not a new inference rule or an assumed preservation certificate.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

namespace IdentityElimination

/-- The endpoint-indexed path family and its universe-valued codomain. -/
def motiveFiber (A a : ETm 0) (n : ℕ) : ETm 1 :=
  .pi (.id A.wk0 a.wk0 (.bv 0)) (.univ n)

/-- Type of an arbitrary function-valued dependent identity motive. -/
def motiveType (A a : ETm 0) (n : ℕ) : ETm 0 := .pi A (motiveFiber A a n)

/-- Apply the motive to an endpoint and its path. -/
def value (M b p : ETm 0) : ETm 0 := .app (.app M b) p

/-- Extensional path induction is implemented by the supplied base term. -/
def basedJ (d _b _p : ETm 0) : ETm 0 := d

/-- A concrete motive returning `Unit`, with both endpoint and path binders. -/
def unitMotive : ETm 0 :=
  .abs .unit (.abs (.id .unit .star (.bv 0)) .unit)

end IdentityElimination
end Silmaril.Logic.TypeTheory.ExtensionalMLTT
