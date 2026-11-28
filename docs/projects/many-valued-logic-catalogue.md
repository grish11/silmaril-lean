# Many-valued logic catalogue

The inventory follows [English Wikipedia, *Many-valued logic*, revision 1387866146
(25 November 2026)](https://en.wikipedia.org/w/index.php?title=Many-valued_logic&oldid=1387866146).
The definitions use arithmetic and order formulas. The reference matrix below
covers the ordered-chain examples in this increment.

Import `Silmaril.Logic.ManyValuedCatalogue.Thms`. All names in the matrix are
relative to `Silmaril.Logic.ManyValuedCatalogue`.

| Article example | Carrier and operations | Checked relationships |
| --- | --- | --- |
| Gödel (G_k), including (G_3) and (G_4) | `Grid n = Fin (n + 2)`, where (k=n+2). Use `Goedel.and`, `or`, `imp`, `neg`, and `designated`. For (G_3) use `Grid 1` and for (G_4) use `Grid 2`. | `Goedel.residuation` identifies the residual of minimum. `UnitInterval.ofGrid_le_iff`, `ofGrid_top`, `ofGrid_bot`, `ofGrid_and`, `ofGrid_or`, `ofGrid_goedelImp`, and `ofGrid_goedelNeg` verify the finite chain's inclusion in the unit interval. |
| Gödel (G_∞) | The same `Goedel` operations on `UnitInterval ℝ`. | `Goedel.residuation` and `Goedel.neg_eq` identify the Heyting residual and the negation that tests the bottom value. The article also discusses axiomatization and completeness. |
| Łukasiewicz (L_v), including (L_3) | `Grid n`, where (v=n+2), with `Grid.lukNeg`, `lukImp`, and `lukAnd`. Use `Grid 1` for (L_3). Only the top value is designated. | `UnitInterval.ofGrid_lukNeg`, `ofGrid_lukImp`, and `ofGrid_lukAnd` verify the numerical interpretation (i/(n+1)) and preservation of all three operations. |
| Rational (L_{ℵ₀}) and real (L_∞) | `UnitInterval ℚ` and `UnitInterval ℝ` with `UnitInterval.lukNeg`, `lukImp`, and `lukAnd`. Only the top value is designated. | `luk_residuation` and `luk_neg_eq` connect the operations. The `ofRat` map reflects order and preserves bounds, negation, implication, and strong conjunction. The article's equality of tautology sets is a separate metatheorem. |
| Product (Π) | `UnitInterval ℝ` with `UnitInterval.prodAnd`, `prodImp`, `prodNeg`, and `prodMeet`. The named falsity constant is bottom. | `prod_residuation` verifies the piecewise residual. `prod_neg_eq` compares residual negations. `prod_meet_eq` proves that (x·(x→y)) gives minimum, while strong conjunction multiplies the degrees. |

The unit interval reuses Mathlib's order on a closed interval. The finite grid
uses integer indices and has two endpoints even at `n = 0`. A degree such as
(1/2) has Łukasiewicz strong conjunction (0) with itself, product strong
conjunction (1/4), and meet (1/2).

The arithmetic operations and the t-norm/residual distinction follow
[Stanford Encyclopedia of Philosophy, *Fuzzy Logic*, §1](https://plato.stanford.edu/entries/logic-fuzzy/#FuzzConnBaseTNorm).
For the finite and infinite systems, see
[Stanford Encyclopedia of Philosophy, *Many-Valued Logic*](https://plato.stanford.edu/entries/logic-manyvalued/).
