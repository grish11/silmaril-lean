module

public import Silmaril.Logic.TypeTheory.LambdaPi.Institution.Thms

@[expose] public section

/-!
# Checked ordered LF signatures

Declarations are checked against the earlier signature, have closed types,
and introduce fresh names. This is the signature discipline for the β-only
LF profile; checking arbitrary rewrite extensions remains a separate task.
-/

namespace Silmaril.Logic.TypeTheory.LambdaPi

/-- A named global declaration. -/
structure Declaration where
  name : String
  type : Term
  deriving DecidableEq

/-- Newest-first declarations; each new type is checked against the older tail. -/
abbrev Signature := List Declaration

namespace Signature

/-- The raw β-only calculus presented by an ordered signature. -/
def calculus (S : Signature) : Calculus :=
  Calculus.lf (fun c A => Declaration.mk c A ∈ S)

/-- Every declaration has a fresh name and a closed, sorted type checked before insertion. -/
inductive Checked : Signature → Prop
  | nil : Checked []
  | cons {S : Signature} {c : String} {A : Term} {s : SortTag}
      (previous : Checked S) (fresh : c ∉ S.map Declaration.name)
      (closed : A.Scoped 0) (sorted : Derives S.calculus ∅ ⟨[], A, Term.univ s⟩) :
      Checked (⟨c, A⟩ :: S)

/-- Signature inclusion supplies a concrete structural calculus translation. -/
def inclusion {S T : Signature} (h : S ⊆ T) : Morphism S.calculus T.calculus where
  constants := id
  declared := by
    intro c A hc
    change Declaration.mk (id c) (A.mapConstants id) ∈ T
    simpa only [Silmaril.Proofs.Logic.TypeTheory.LambdaPi.map_id, id_eq] using h hc
  rules r hr := (Set.notMem_empty r hr).elim

end Signature

/-- An LF signature with its actual declaration derivations. -/
structure CheckedSignature where
  declarations : Signature
  checked : declarations.Checked

/-- The underlying raw calculus, retaining all declarations. -/
abbrev CheckedSignature.calculus (S : CheckedSignature) : Calculus := S.declarations.calculus

end Silmaril.Logic.TypeTheory.LambdaPi
