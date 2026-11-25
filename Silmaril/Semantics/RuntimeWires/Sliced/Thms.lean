module

public import Silmaril.Semantics.RuntimeWires.Sliced.Interpretation
import Silmaril.Proofs.Semantics.RuntimeWires.Sliced.Soundness
import Silmaril.Proofs.Semantics.RuntimeWires.Sliced.Vertices

@[expose] public section

/-!
Each seam move has sound interpretation in the existing monoidal quotient.
For comparison with progressive plane graphs, the remaining work is to
realize typed sheets as embedded graphs, slice arbitrary progressive
embeddings, and show that changing the slices or deforming the embedding
induces the permitted moves. Algebraic completeness also needs
representability of quotient arrows and reflection of equality for the
presentation with no extra equations. Figure 9 runtime equations require a
separate family of moves on labeled boxes, as the seam moves preserve the
number of vertices.
-/

namespace Silmaril.RuntimeWires.Sliced

open CategoryTheory

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {A M B : List O}

/-- Two rows formed by a seam through a single row compose to its interpretation. -/
theorem Row.Split.sound {r : Row S A B} {p : Row S A M} {q : Row S M B}
    (h : Row.Split S r p q) (E : Diagram.Equations S) :
    r.denote E = p.denote E ≫ q.denote E :=
  Proofs.Sliced.denote_split E h

/-- Elementary seam moves preserve the corresponding quotient arrow. -/
theorem Sheet.Move.sound {p q : Sheet S A B} (h : Sheet.Move S p q)
    (E : Diagram.Equations S) : p.denote E = q.denote E :=
  Proofs.Sliced.denote_move E h

/-- Soundness of the sliced model. A sequence of seam deformations preserves
interpretation in any algebraic presentation over the same signature. -/
theorem Sheet.SeamEquivalent.sound {p q : Sheet S A B} (h : Sheet.SeamEquivalent p q)
    (E : Diagram.Equations S) : p.denote E = q.denote E :=
  Proofs.Sliced.denote_seam E h

/-- Seam moves preserve vertices, including nullary boxes. -/
theorem Sheet.SeamEquivalent.boxCount_eq {p q : Sheet S A B} (h : Sheet.SeamEquivalent p q) :
    p.boxCount = q.boxCount :=
  Proofs.Sliced.count_seam h

end Silmaril.RuntimeWires.Sliced
