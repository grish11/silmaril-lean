module

public import Silmaril.Logic.TypeTheory.LambdaPi.Signature.Thms

@[expose] public section

/-!
# Term-valued translations of λΠ-modulo presentations

An assignment replaces global constants by closed terms. An encoding supplies
actual target typings for declared constants and target conversions for source
rewrite schemas. Preservation of all typing rules is a theorem, not a field.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- Closed images allow the same assignment beneath every local binder. -/
structure ConstantAssignment where
  constants : String → Term
  closed : ∀ c, (constants c).Scoped 0

namespace ConstantAssignment

/-- Replace global constants, fixing sorts, variables and binding structure. -/
def term (F : ConstantAssignment) : Term → Term
  | .sort (.sort s) => Term.univ s
  | .sort (.constant c) => F.constants c
  | .var i => .var i
  | .app f a => .app (F.term f) (F.term a)
  | .lam A b => .lam (F.term A) (F.term b)
  | .pi A B => .pi (F.term A) (F.term B)

/-- Translate the local context, subject and type of a hypothetical judgment. -/
def judgment (F : ConstantAssignment) (J : Judgment) : Judgment :=
  ⟨J.context.map F.term, F.term J.term, F.term J.type⟩

end ConstantAssignment

/-- A raw presentation whose declaration types have actual sorting derivations.

Rewrite admissibility, normalization and consistency remain separate properties.
-/
structure TypedPresentation where
  calculus : Calculus
  sorted : ∀ {c A}, calculus.declared c A →
    ∃ s, Derives calculus ∅ ⟨[], A, Term.univ s⟩

/-- A translation may implement constants by compound target terms.

Source rewrite schemas need only become target conversions; the target need
not contain the same rewrite rule, or any user rewrite rules at all.
-/
structure Encoding (C D : TypedPresentation) extends ConstantAssignment where
  declared : ∀ {c A}, C.calculus.declared c A →
    Derives D.calculus ∅ ⟨[], constants c, toConstantAssignment.term A⟩
  rules : ∀ r ∈ C.calculus.rules,
    D.calculus.Conversion (toConstantAssignment.term r.lhs) (toConstantAssignment.term r.rhs)

end Silmaril.Logic.TypeTheory.LambdaPi
