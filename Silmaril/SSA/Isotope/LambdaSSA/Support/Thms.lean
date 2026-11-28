module

public import Silmaril.SSA.Isotope.LambdaSSA.Support.Defs
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.RegionScope
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Support.Occurrences

public section

namespace Silmaril.DeBruijn

/-- Under new binders, a bound on free indices is equivalent to a bound
on the corresponding older indices before they were shifted. -/
theorem older_bound (p : Nat → Prop) (n d : Nat) :
    (∀ i, p i → i < n + d) ↔ ∀ i, p (i + d) → i < n :=
  Proofs.SSA.Isotope.LambdaSSA.Support.older_bound p n d

end Silmaril.DeBruijn

namespace Silmaril.Isotope.LambdaSSA.Tm

universe u
variable {Φ : Type u}

/-- Renaming maps exactly the free value-variable occurrences. -/
theorem usesVar_rename (t : Tm Φ) (ρ : Nat → Nat) (i : Nat) :
    (t.rename ρ).UsesVar i ↔ ∃ j, t.UsesVar j ∧ ρ j = i :=
  Proofs.SSA.Isotope.LambdaSSA.Support.usesVar_rename t ρ i

/-- Expression scoping bounds precisely the free value-variable indices. -/
theorem scoped_iff_usesVar_lt (t : Tm Φ) (n : Nat) :
    t.Scoped n ↔ ∀ i, t.UsesVar i → i < n :=
  Proofs.SSA.Isotope.LambdaSSA.Support.scoped_iff t n

end Silmaril.Isotope.LambdaSSA.Tm
