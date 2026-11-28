module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Join.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomSource

/-! # Written source graphs and spelled trees

A written source graph is a checked captured table: rows with one block
parameter each, reading the ambient captures and their own packet, ending
in a jump or a case, with ordered exits. A join is a row that several rows
jump to; its block parameter is the phi. A value that is live across rows
and is not an ambient capture is passed in the packets. The table is
written by hand; it is not read back from a LetCase term.

The ranked sentences are between entries of such tables. The emitted
operand of an entry is the checked readback of the table, which unfolds a
join row once into each of its predecessors. When that readback is
natively equal to a spelled tree, the ranked theorems of the spelled
grammar apply to the source graph itself: validity of a sentence between
two such entries, at their original entry and original ordered exits, is
equality of the normal forms of the two trees, and it is decided by the
ordered trace model with atoms.

The native equation between the readback of a table and a tree is given
per table. No theorem here computes it from the shape of the table.

The theorem that readback commutes with linking two written graphs, so
that a later graph reads the result of an earlier one as a positional
capture, is proved for the finite structural signatures over the types
without atoms, through their finite separator. It is not available for the
signatures with atoms used here. A value produced inside one written graph
and used in a later row is therefore passed in the packets of that graph.
-/

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

/-- The entry of a written graph whose readback is natively equal to a
spelled tree emits a spelled operand. -/
theorem spelledOperand_of_readback {t : LetCase.LocallyNameless.Tm Empty Φ n} (G : CheckedTable Φ β L) (d : Spelled β L t)
    (same : Equiv false Γ₀ β G.toLetCase.1 t (packedExitType L)) :
    SpelledOperand (emitted (P := atomSig α Φ) (entryOf G)) :=
  ⟨t, d, same⟩

/-- A ranked sentence between two entries whose emitted operands are
natively equal to spelled trees is valid exactly when the two trees have
the same normal form. The entries may be entries of written source graphs
or of graphs read back from terms. -/
theorem rankedValid_entries_iff {t u : LetCase.LocallyNameless.Tm Empty Φ n} (separable : Separable β)
    (l r : RankedEntry Φ β L) (p : Spelled β L t) (q : Spelled β L u)
    (hl : Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 t (packedExitType L))
    (hr : Equiv false Γ₀ β (emitted (P := atomSig α Φ) r).1 u (packedExitType L)) :
    RankedValid false (sentenceOf l r) ↔ (p.normal (.id β)).1 = (q.normal (.id β)).1 :=
  rankedValid_entries_iff_proof separable l r p q hl hr

/-- At the ordered trace model with atoms, two such entries have the same
ordered-exit arrow exactly when the two trees have the same normal form. -/
theorem denoteRanked_entries_iff {t u : LetCase.LocallyNameless.Tm Empty Φ n} (separable : Separable β)
    (l r : RankedEntry Φ β L) (p : Spelled β L t) (q : Spelled β L u)
    (hl : Equiv false Γ₀ β (emitted (P := atomSig α Φ) l).1 t (packedExitType L))
    (hr : Equiv false Γ₀ β (emitted (P := atomSig α Φ) r).1 u (packedExitType L)) :
    denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) l =
        denoteRanked (traceJ (α := α) (Φ := Φ)) (atomTraceModel α Φ) r ↔
      (p.normal (.id β)).1 = (q.normal (.id β)).1 :=
  denoteRanked_entries_iff_proof separable l r p q hl hr

/-- Two written source graphs whose readbacks are natively equal to
spelled trees are valid together, at their original entries and original
ordered exits, exactly when the two trees have the same normal form. -/
theorem rankedValid_sources_iff {t u : LetCase.LocallyNameless.Tm Empty Φ n} (separable : Separable β)
    (G H : CheckedTable Φ β L) (p : Spelled β L t) (q : Spelled β L u)
    (hG : Equiv false Γ₀ β G.toLetCase.1 t (packedExitType L))
    (hH : Equiv false Γ₀ β H.toLetCase.1 u (packedExitType L)) :
    RankedValid false (sentenceOf (entryOf G) (entryOf H)) ↔
      (p.normal (.id β)).1 = (q.normal (.id β)).1 :=
  rankedValid_entries_iff separable (entryOf G) (entryOf H) p q hG hH

/-- A written source graph whose readback is natively equal to a spelled
tree and the graph of a spelled tree are valid together exactly when the
two trees have the same normal form. -/
theorem rankedValid_source_iff {t u : LetCase.LocallyNameless.Tm Empty Φ n} (separable : Separable β)
    (G : CheckedTable Φ β L) (p : Spelled β L t) (q : Spelled β L u)
    (hG : Equiv false Γ₀ β G.toLetCase.1 t (packedExitType L)) :
    RankedValid false (sentenceOf (entryOf G) (entryOf q.graph)) ↔
      (p.normal (.id β)).1 = (q.normal (.id β)).1 :=
  rankedValid_entries_iff separable (entryOf G) (entryOf q.graph) p q hG
    (CheckedTable.ofLetCase_emit false q.exits_ne_nil q.typing)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
