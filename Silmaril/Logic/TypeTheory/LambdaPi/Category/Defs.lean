module

public import Silmaril.Logic.TypeTheory.LambdaPi.Thms
public import Silmaril.Logic.Institution.Metatheory.Entailment

@[expose] public section

namespace Silmaril.Logic.TypeTheory.LambdaPi

open CategoryTheory

/-- Translate the names in a rewrite schema without changing its binder budget. -/
def RewriteRule.mapConstants (f : String → String) (r : RewriteRule) : RewriteRule where
  arity := r.arity
  lhs := r.lhs.mapConstants f
  rhs := r.rhs.mapConstants f
  lhs_scoped := Silmaril.Proofs.Logic.TypeTheory.LambdaPi.map_scoped f _ r.lhs_scoped
  rhs_scoped := Silmaril.Proofs.Logic.TypeTheory.LambdaPi.map_scoped f _ r.rhs_scoped

/-- A structural translation preserving declarations and each rewrite schema.

This first category uses constant-name maps. General encodings of a constant
by a term are a larger translation class, not silently identified with these maps.
-/
structure Morphism (C D : Calculus) where
  constants : String → String
  declared : ∀ {c A}, C.declared c A → D.declared (constants c) (A.mapConstants constants)
  rules : ∀ r ∈ C.rules, r.mapConstants constants ∈ D.rules

end Silmaril.Logic.TypeTheory.LambdaPi
