module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite

@[expose] public section

/-!
# Object-term templates for the W/equality encoding

These are terms of the existing extensional MLTT-with-W grammar, not new
primitive indexed inductives. This module checks scopes and explicit universe
occurrences; derivability and agreement with the Type equivalence are separate
obligations. In particular a bounded template alone is not a bounded proof.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- An object indexed-container description, using de Bruijn indices inward first. -/
structure Description where
  /-- The index type, in the surrounding free-variable context. -/
  index : Tm 0
  /-- Shapes, under the result index `i`. -/
  shape : Tm 1
  /-- Positions, under a shape `a` (index 0) and result index `i` (index 1). -/
  position : Tm 2
  /-- Requested child index, under `p` (0), `a` (1), and `i` (2). -/
  next : Tm 3

namespace Description

def totalShape (S : Description) : Tm 0 := .sigma S.index S.shape

/-- Positions of a tagged shape; both original description binders are replaced. -/
def positions (S : Description) : Tm 1 :=
  S.position.bsubst (Fin.cases (.snd (.bv 0)) (fun _ => .fst (.bv 0)))

def raw (S : Description) : Tm 0 := .wtype S.totalShape S.positions

/-- The child-function annotation under a single tagged-shape binder. -/
def childrenType (S : Description) : Tm 1 :=
  .pi S.positions (S.raw.castLE (by decide))

/-- Step for root-index projection; `ih`, `children`, `label` have indices 0, 1, 2. -/
def rootStep (S : Description) : Tm 0 :=
  .abs S.totalShape (.abs S.childrenType
    (.abs (.pi (S.positions.bsubst (fun _ => .bv 1)) (S.index.castLE (by decide)))
      (.fst (.bv 2))))

/-- Root index, obtained by ordinary W elimination with a constant motive. -/
def root {k : ℕ} (S : Description) (t : Tm k) : Tm k :=
  .wrec (S.totalShape.castLE (by omega)) (S.positions.castLE (by omega))
    (S.index.castLE (by omega)) (S.rootStep.castLE (by omega)) t

/-- Instantiate the three description binders with a tagged label and a position. -/
def childIndexAt {k : ℕ} (S : Description) (label p : Tm k) : Tm k :=
  S.next.bsubst (Fin.cases p (Fin.cases (.snd label) (fun _ => .fst label)))

/-- Coherence result type under `ih`, `children`, `label`.

For each position it records the child's requested index equation and the
recursive coherence witness. Thus it checks every edge, through `ih`.
-/
def coherenceBody (S : Description) : Tm 3 :=
  .pi (S.positions.bsubst (fun _ => .bv 2))
    (.sigma
      (.id (S.index.castLE (by decide))
        (S.root (.app (.bv 2) (.bv 0)))
        (S.childIndexAt (.bv 3) (.bv 0)))
      (.app (.bv 2) (.bv 1)))

/-- Type-valued coherence recursion. Its constant motive is the object universe `Uₙ`. -/
def coherenceStep (S : Description) (n : ℕ) : Tm 0 :=
  .abs S.totalShape (.abs S.childrenType
    (.abs (.pi (S.positions.bsubst (fun _ => .bv 1)) (.univ n)) S.coherenceBody))

def coherence {k : ℕ} (S : Description) (n : ℕ) (t : Tm k) : Tm k :=
  .wrec (S.totalShape.castLE (by omega)) (S.positions.castLE (by omega))
    (.univ n) ((S.coherenceStep n).castLE (by omega)) t

/-- The encoded fibre: a raw W-tree, its result-index equation, and all-edge coherence. -/
def fibre (S : Description) (n : ℕ) (i : Tm 0) : Tm 0 :=
  .sigma S.raw
    (.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
      (S.coherence n (.bv 1)))

def positionAt (S : Description) (i a : Tm 0) : Tm 0 :=
  S.position.bsubst (Fin.cases a (fun _ => i))

/-- Object constructor template, erasing each child's fibre witness into the raw W-node. -/
def node (S : Description) (i a f : Tm 0) : Tm 0 :=
  .pair (.sup S.totalShape S.positions (.pair i a)
      (.abs (S.positionAt i a) (.fst (.app f.wk0 (.bv 0)))))
    (.pair (.refl i) (.abs (S.positionAt i a) (.snd (.app f.wk0 (.bv 0)))))

/-- A bound on all universe occurrences in the input description. -/
def universeBound (S : Description) : ℕ :=
  max (max S.index.universeBound S.shape.universeBound)
    (max S.position.universeBound S.next.universeBound)

end Description

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
