module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Join.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation RankedEntry denoteRanked)
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Derivation Equiv HasType)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} [TaggedSignature α Φ] {n : Nat} {β : BoundCtx (Ty α) n} {L : List (Ty α)}

/-- A ranked sentence between two entries whose emitted operands are
natively equal to spelled trees is valid exactly when the two trees have
the same normal form. -/
theorem rankedValid_entries_iff_proof {t u : LetCase.LocallyNameless.Tm Empty Φ n} (separable : Separable β)
    (l r : RankedEntry Φ β L) (p : Spelled β L t) (q : Spelled β L u)
    (hl : Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 t (packedExitType L))
    (hr : Equiv false Γ₀ β (emitted (P := atomSig α Φ) r).1 u (packedExitType L)) :
    RankedValid false (sentenceOf l r) ↔ (p.normal (.id β)).1 = (q.normal (.id β)).1 :=
  (rankedValid_spelled_iff separable l r ⟨t, p, hl⟩ ⟨u, q, hr⟩).trans
    (Iff.trans ⟨fun h => (hl.symm.trans h).trans hr, fun h => (hl.trans h).trans hr.symm⟩
      (spelled_equiv_iff_normal separable p q))

/-- At the ordered trace model with atoms, two such entries have the same
ordered-exit arrow exactly when the two trees have the same normal form. -/
theorem denoteRanked_entries_iff_proof {t u : LetCase.LocallyNameless.Tm Empty Φ n} (separable : Separable β)
    (l r : RankedEntry Φ β L) (p : Spelled β L t) (q : Spelled β L u)
    (hl : Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 t (packedExitType L))
    (hr : Equiv false Γ₀ β (emitted (P := atomSig α Φ) r).1 u (packedExitType L)) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) l =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) r ↔
      (p.normal (.id β)).1 = (q.normal (.id β)).1 :=
  (rankedValid_spelled_iff_atomTrace separable l r ⟨t, p, hl⟩ ⟨u, q, hr⟩).symm.trans
    (rankedValid_entries_iff_proof separable l r p q hl hr)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
