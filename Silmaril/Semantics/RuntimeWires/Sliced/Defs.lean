module

public import Silmaril.Semantics.RuntimeWires.Polygraph.Defs
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# Ordered slices of progressive diagrams

This is a combinatorial model for the seam moves used in a comparison with
Definition 3.2, Lemma 3.4, Theorem 3.6 and Corollary 3.15 of Mario Román and
Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5, pp. 9:6–9:8, 9:13. Figure 7 illustrates the horizontal
and vertical operations motivating the model.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.

A row records the left-to-right order of its disjoint boxes and through
wires. Two rows can meet only at a common ordered, typed frontier.
The seam relation below is defined on this syntax without referring to
monoidal terms or their congruence.
-/

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u}

/-- One row of disjoint boxes and through wires, in left-to-right order.
A box uses a contiguous block on each frontier. A box with an empty input or output still occupies
a position in the row. -/
inductive Row (S : Signature.{u,v} O) : List O → List O → Type (max u v)
  | empty : Row S [] []
  | wire (x : O) {A B : List O} : Row S A B → Row S (x :: A) (x :: B)
  | box (e : S.Edge) {A B : List O} : Row S A B →
      Row S (S.source e ++ A) (S.target e ++ B)

variable {S : Signature.{u,v} O}

namespace Row

/-- Put through wires on the left, in their given order. -/
def pass (W : List O) {A B : List O} (row : Row S A B) : Row S (W ++ A) (W ++ B) :=
  match W with
  | [] => row
  | x :: W => .wire x (pass W row)

/-- A row without boxes. -/
def straight (W : List O) : Row S W W :=
  match W with
  | [] => .empty
  | x :: W => .wire x (straight W)

/-- Count the labeled vertices in the row. -/
def boxCount : {A B : List O} → Row S A B → Nat
  | _, _, .empty => 0
  | _, _, .wire _ r => boxCount r
  | _, _, .box _ r => boxCount r + 1

/-- A witness for drawing a new horizontal seam through a row. Wire cells
continue through both slices. Each box lies wholly above or wholly below the
seam. The intermediate frontier contains its outputs in the former case and
its inputs in the latter. -/
inductive Split (S : Signature.{u,v} O) :
    {A M B : List O} → Row S A B → Row S A M → Row S M B → Prop
  | empty : Split S .empty .empty .empty
  | wire (x : O) {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B} :
      Split S r p q → Split S (.wire x r) (.wire x p) (.wire x q)
  | upper (e : S.Edge) {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B} :
      Split S r p q → Split S (.box e r) (.box e p) (pass (S.target e) q)
  | lower (e : S.Edge) {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B} :
      Split S r p q → Split S (.box e r) (pass (S.source e) p) (.box e q)

end Row

/-- A top-to-bottom sequence of rows with matching ordered seams. -/
inductive Sheet (S : Signature.{u,v} O) : List O → List O → Type (max u v)
  | empty (A : List O) : Sheet S A A
  | cons {A M B : List O} : Row S A M → Sheet S M B → Sheet S A B

namespace Sheet

/-- Count the labeled vertices independent of the number of seams. -/
def boxCount : {A B : List O} → Sheet S A B → Nat
  | _, _, .empty _ => 0
  | _, _, .cons row rest => row.boxCount + boxCount rest

/-- Elementary changes of slicing. A move acts at the top seam or below a
common prefix of rows. -/
inductive Move (S : Signature.{u,v} O) :
    {A B : List O} → Sheet S A B → Sheet S A B → Prop
  | split {A M N B : List O} {r : Row S A N} {p : Row S A M} {q : Row S M N}
      (h : Row.Split S r p q) (tail : Sheet S N B) :
      Move S (.cons r tail) (.cons p (.cons q tail))
  | straight {A B : List O} (tail : Sheet S A B) :
      Move S tail (.cons (Row.straight A) tail)
  | under {A M B : List O} (r : Row S A M) {p q : Sheet S M B} :
      Move S p q → Move S (.cons r p) (.cons r q)

/-- Two slices are related by reversible seam moves at fixed external
frontiers. This is a combinatorial relation on sheets. -/
abbrev SeamEquivalent {A B : List O} : Sheet S A B → Sheet S A B → Prop :=
  Relation.EqvGen (Move S)

end Sheet

end Silmaril.RuntimeWires.Sliced
