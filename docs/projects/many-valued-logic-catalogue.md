# Many-valued logic catalogue

The inventory follows [English Wikipedia, *Many-valued logic*, revision 1387866146
(25 November 2026)](https://en.wikipedia.org/w/index.php?title=Many-valued_logic&oldid=1387866146).
The matrices identify the operations and observations specified by the article.
The definitions use arithmetic, order, or Boolean formulas.

Import `Silmaril.Logic.ManyValuedCatalogue.Thms` for the chain families and
`Silmaril.Logic.ManyValuedCatalogue.Discrete.Thms` for the discrete and application
encodings. Names are relative to `Silmaril.Logic.ManyValuedCatalogue` unless a row
names another module.

## Ordered chains

| Article example | Carrier and operations | Checked relationships |
| --- | --- | --- |
| Gödel Gₖ, including G₃ and G₄ | `Grid n = Fin (n + 2)`, where `k = n + 2`. Use `Goedel.and`, `or`, `imp`, `neg`, and `designated`. For G₃ use `Grid 1` and for G₄ use `Grid 2`. | `Goedel.residuation` identifies the residual of minimum. `UnitInterval.ofGrid_le_iff`, `ofGrid_top`, `ofGrid_bot`, `ofGrid_and`, `ofGrid_or`, `ofGrid_goedelImp`, and `ofGrid_goedelNeg` verify the finite chain's inclusion in the unit interval. |
| Gödel G∞ | The same `Goedel` operations on `UnitInterval ℝ`. | `Goedel.residuation` and `Goedel.neg_eq` identify the Heyting residual and the negation that tests the bottom value. The article also discusses axiomatization and completeness. |
| Łukasiewicz Lᵥ, including L₃ | `Grid n`, where `v = n + 2`, with `Grid.lukNeg`, `lukImp`, and `lukAnd`. Use `Grid 1` for L₃. Only the top value is designated. | `UnitInterval.ofGrid_lukNeg`, `ofGrid_lukImp`, and `ofGrid_lukAnd` verify the numerical interpretation `i/(n+1)` and preservation of all three operations. |
| Rational Lℵ₀ and real L∞ | `UnitInterval ℚ` and `UnitInterval ℝ` with `UnitInterval.lukNeg`, `lukImp`, and `lukAnd`. Only the top value is designated. | `luk_residuation` and `luk_neg_eq` connect the operations. The `ofRat` map reflects order and preserves bounds, negation, implication, and strong conjunction. The article's equality of tautology sets is a separate metatheorem. |
| Product Π | `UnitInterval ℝ` with `UnitInterval.prodAnd`, `prodImp`, `prodNeg`, and `prodMeet`. The named falsity constant is bottom. | `prod_residuation` verifies the piecewise residual. `prod_neg_eq` compares residual negations. `prod_meet_eq` proves that `x · (x → y)` gives minimum, while strong conjunction multiplies the degrees. |

The unit interval reuses Mathlib's order on a closed interval. The finite grid
uses integer indices and has two endpoints even at `n = 0`. A degree such as
1/2 has Łukasiewicz strong conjunction 0 with itself, product strong
conjunction 1/4, and meet 1/2.

## Discrete examples

| Article example | Carrier and operations | Checked relationships |
| --- | --- | --- |
| Strong Kleene K3 | `Silmaril.Logic.ManyValued.K3` with `neg`, `conj`, `disj`, `materialImp`, `materialIff`, and `isDesignated`. `tt` alone is designated. | C5 checks all five tables and the Boolean embedding. Its `K3.toOptionBool` and `K3.ofOptionBool` identify the carrier of K3 with `Bochvar`. [C5 definitions](../../Silmaril/Logic/ManyValued/Defs.lean) and [checked tables](../../Silmaril/Logic/ManyValued/Examples.lean) |
| Priest P3 (LP) | Use the same K3 operations, with designation `x ≠ K3.ff`. Equivalently take the FDE truth subalgebra on `ff`, `both`, and `tt`, with FDE designation. On that subalgebra, material implication is `disj (neg x) y` and biconditional is the conjunction of the two directions. | C5 checks that the relabeling sending K3's `unknown` to FDE's `both` preserves negation, conjunction, disjunction, and the stated designation, which also gives preservation of the two derived operations by composition. [C5 checked LP restriction](../../Silmaril/Logic/ManyValued/Examples.lean#L67-L79) |
| Bochvar internal logic (weak Kleene) | `Bochvar = Option Bool`, with `none` for the intermediate degree and `some true` designated. `Bochvar.and`, `or`, and `imp` lift the three Boolean operations to the infectious tables. `Bochvar.neg` and `iff` encode the other two connectives. | `lift₂_none_left`, `lift₂_none_right`, and `lift₂_eq_some_iff` give every entry from the Boolean operations and the infectious value. `k3_neg`, `k3_materialIff`, and `k3_designated` prove preservation of these observations under `K3.toOptionBool`. `toGrid_neg` and `toGrid_iff` also verify their numerical forms. `and_unknown` witnesses a difference for conjunction. The scope is Bochvar's internal fragment. |
| Belnap B4 / FDE | `Silmaril.Logic.ManyValued.FDE`, with `tt`, `both`, `neither`, and `ff` for T, B, N, and F. Use `neg`, `conj`, and `disj` for the three article tables and `isDesignated` for the positive evidence observation. | C5 checks the three truth tables and the partial Boolean observation. The knowledge order records evidence refinement. [C5 definitions](../../Silmaril/Logic/ManyValued/Defs.lean) and [checked tables](../../Silmaril/Logic/ManyValued/Examples.lean) |
| Post Pₘ | `Grid n`, where `m = n + 2`, with `Post.neg`, `and`, and `or`. Supply the size of the designated upper segment to `Post.designated` when using a matrix variant. | `Post.neg_val` gives the wraparound predecessor, and `neg_bijective` checks that it is a permutation. `designated_one` checks the top-only variant. Post orders the original subscripts in descending truth order and takes cyclic negation and maximum as generators. [Post 1921, pp. 180–181](https://doi.org/10.2307/2370324) |
| Rose lattice-valued systems | `Rose.and` and `or` are meet and join on a bounded lattice. `Rose.imp` tests the top antecedent and `Rose.neg` uses bottom as consequent. `Rose.swapTop` exchanges the top and a chosen intermediate value. `Rose.Diamond 3` is the five-element example in Figure 3. | `swapTop_top` and `swapTop_self` check the swap. `diamond_distributivity_formula` verifies Rose's assignment that makes his distributivity formula evaluate to an atom. `imp_middle` distinguishes Rose's implication from Gödel's on the three-element chain. [Rose 1951, pp. 153–154](https://doi.org/10.1007/BF02054946) |
| Classical two-valued algebra | `Bool` with `Bool.not`, `Bool.and`, `Bool.or`, `Bool.or (Bool.not a) b`, and Boolean equality for the five displayed connectives. | The injection `some` into `Bochvar` commutes with the unary operation by reduction and with the binary operations by `Bochvar.lift₂_eq_some_iff`. C5 also checks its classical embeddings. |

## Applications

| Article example or mention | Scope and reference |
| --- | --- |
| Boolean multi-output function as one multi-valued output and a characteristic function | Take output type `Fin k → Bool` in `graphIndicator`. `graphIndicator_unique` proves that the Boolean graph indicator singles out the original output for each input. [Dubrova 2002, pp. 89–114](https://doi.org/10.1007/978-1-4615-0817-5_4) |
| Five-valued circuit fault simulation (ATPG, also called ATG in the article) | `FaultValue` is a joint observation with projections `faultFree` and `faulty`. In that order, `d` represents (1, 0) and `dBar` represents (0, 1), so D reads as a faulty 0 in place of a fault-free 1. `zero`, `one`, and `unknown` give the other observations. `FaultValue.distinct`, `exhaustive`, and `observations_injective` check the alphabet and its decoder. Coverage ends at these observations. [Roth 1966, pp. 278–291](https://doi.org/10.1147/rd.104.0278) |
| Qudits, synthesis and optimization of qudit circuits, and photonic frequency, orbital angular momentum, and time-bin encodings | `Qudit.basis` gives the computational basis indexed by `Fin d`. Take complex amplitudes and `2 < d`. `relabel_basis` and `relabel_inverse` check the action of basis permutations. Capacities, security, physical encodings, and general gates are application context. [Erhard, Krenn, and Zeilinger 2020, §§II–III](https://arxiv.org/abs/1911.10006v2) |
| Programmable logic arrays with input decoders, FSM optimization, testing, and verification | Application classes. The article names workflows and gives the graph indicator and the fault alphabet as separately specified examples. |
| Multilevel memories, arithmetic circuits, FPGAs, four-or-more-level interconnects and two bits per cell | Application claims about representation or hardware realization. The article supplies no gate signature for these classes. |
| Residue and redundant number systems | Arithmetic representations mentioned in the context of carries. Their arithmetic depends on the chosen moduli or digit representation. |
| IEEE 1164, IEEE 1364, and three-state logic | See C6's `Silmaril.Logic.DigitalSimulation.StdULogic` for nine VHDL values and `VerilogBit` for four Verilog/SystemVerilog scalar values. Its scalar gate and resolution contracts specify the IEEE editions and drive assumptions. The three-state mention concerns the `zero`, `one`, `z` output alphabet. [C6 scope and definitions](ieee-digital-simulation.md) |
| Multiple-valued current-mode logic (MVCML) and noise-based logic | See-also links to physical signal encodings. The cited revision gives no truth-operation specification. |

## Historical, family, and metatheorem mentions

| Article mention | Scope and reference |
| --- | --- |
| Aristotle, future contingents, and the sea battle | Motivation for the use of a third value. The concrete three-valued Łukasiewicz algebra is in the ordered-chain matrix. |
| Łukasiewicz–Tarski finite degrees and Post's historical finite systems | The finite Łukasiewicz and Post rows give their algebraic coverage. |
| Reichenbach's infinite-valued work and probability logic | The history and lead give no particular carrier-and-connective signature. Probability logics may describe probabilities of propositions in richer languages. [Demey, Kooi, and Sack, *Logic and Probability*](https://plato.stanford.edu/entries/logic-probability/) |
| Intuitionistic logic, intermediate logics, justification, and excluded middle | Logical families and historical motivation. The finite and infinite Gödel rows supply the specified algebras. Gödel's result that no finite truth matrix characterizes intuitionistic logic is a metatheorem. |
| Fuzzy logic and degrees of truth | Family names. The Gödel, Łukasiewicz, and product rows give the specified standard t-norm interpretations. [SEP, *Fuzzy Logic*, §1](https://plato.stanford.edu/entries/logic-fuzzy/#FuzzConnBaseTNorm) |
| K3 and LP tautologies, Gödel axiomatizability and completeness, and real/rational Łukasiewicz tautology equality | Metatheoretic claims about languages or proof systems. The checked results in the matrices are algebraic operations, designation, and inclusions. K3 and LP tautology statements refer to the displayed constant-free signature. |
| Suszko's thesis, bivalence, and designated values | The designated sets appear in the algebraic rows. Suszko's thesis is a claim about semantic consequence and its representations. |
| Functional completeness, adequacy, Post's generation argument, and the general finite matrix schema | Metatheory about expressibility and iteration of finitary operations. The classical and Post rows give the named algebraic signatures. |
| Three-, four-, seven-, nine-, finite-, and infinite-valued logic | Cardinality descriptions. Concrete occurrences appear in the ordered-chain, discrete, and application matrices. |
| Jaina seven-valued logic | See-also reference to seven qualified modes of predication formed from existence, nonexistence, and inexpressibility. The article gives no operations on them. [Gorisse, *Jaina Philosophy*, §3.4.3](https://plato.stanford.edu/entries/jaina-philosophy/#ExisNonExisModePred) |
| Mathematical and philosophical logic, MV-algebra, Kleene algebra with involution, relevance logic, A. N. Prior, false dilemma, and Mu | See-also references to general subjects, algebraic classes, people, and concepts. Gödel, Łukasiewicz, Kleene, Belnap, fuzzy, and Post links point back to the rows above. |
| Symposium, journal, bibliography, external links, and navigation template | Research venues and bibliographic/navigation items. |

## Sources

Each hash identifies the cited artifact as fetched on 28 November 2026.
Crossref entries identify the bibliographic record.

| Source and locator | SHA-256 |
| --- | --- |
| Wikipedia contributors, [*Many-valued logic*, revision 1387866146, Examples](https://en.wikipedia.org/w/index.php?title=Many-valued_logic&oldid=1387866146#Examples), 25 November 2026 | `4672835704f69c91d551f998c0d295400571ff38cbea79aff59668017af6c4a9` |
| Petr Cintula, Christian G. Fermüller, and Carles Noguera, [*Fuzzy Logic*, §1](https://plato.stanford.edu/entries/logic-fuzzy/#FuzzConnBaseTNorm), Stanford Encyclopedia of Philosophy, 11 November 2021 revision | `dda00ba425fc31648f9553e88d53845383c496edd740d9e38f39952213c041c7` |
| João Marcos, Adam Přenosil, and Paul Égré, [*Many-Valued Logic*, §§2.1 and 3.2.2](https://plato.stanford.edu/entries/logic-manyvalued/), Stanford Encyclopedia of Philosophy, 29 September 2026 revision | `5a549597b7c78fe2d5d3252f0bc4bcf0e1e48afeff6314e1f05a9dd505773169` |
| Emil L. Post, [*Introduction to a General Theory of Elementary Propositions*](https://doi.org/10.2307/2370324), 1921, pp. 180–181. [JSTOR Early Journal Content PDF](https://archive.org/download/jstor-2370324/2370324.pdf) | `8e51d5287f7126772db0096e79f6ded522ce899ab2b2628c97f7b2a795456868` |
| Alan Rose, [*Systems of logic whose truth-values form lattices*](https://doi.org/10.1007/BF02054946), 1951, pp. 153–154. [Göttingen digitized PDF](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0123/LOG_0013.pdf) | `bcb68489c1d9255949e985cb99744542b534eeedca244c069f59eb2cc7fdfee0` |
| Elena Dubrova, [*Multiple-Valued Logic Synthesis and Optimization*](https://doi.org/10.1007/978-1-4615-0817-5_4), 2002, pp. 89–114. [Crossref JSON](https://api.crossref.org/works/10.1007/978-1-4615-0817-5_4) | `a776276e22e4bad66d9a2deddbec51aa8cd7909f684baf513f7d19b79063298e` |
| J. Paul Roth, [*Diagnosis of Automata Failures: A Calculus and a Method*](https://doi.org/10.1147/rd.104.0278), 1966, pp. 278–291. [Crossref JSON](https://api.crossref.org/works/10.1147/rd.104.0278) | `9bfab6ac1b3712be3ed07a318e0118cc18ff43f5cdcc146bd9c126a7fdb64e58` |
| Manuel Erhard, Mario Krenn, and Anton Zeilinger, [*Advances in High-Dimensional Quantum Entanglement*](https://arxiv.org/abs/1911.10006v2), 28 November 2019 arXiv revision, §§II–III. [PDF](https://arxiv.org/pdf/1911.10006v2) | `19230b778d97f0561b6de1a6b918fb6369dec46d12716c76bd2e966c95cf837e` |
| Marie-Hélène Gorisse, [*Jaina Philosophy*, §3.4.3](https://plato.stanford.edu/entries/jaina-philosophy/#ExisNonExisModePred), Stanford Encyclopedia of Philosophy, 13 February 2023 HTML | `fbda54e0bb711b2413a9c51af408dcf354b8b9b80332ac1278b0ceebeb56b4b8` |
| Lorenz Demey, Barteld Kooi, and Joshua Sack, [*Logic and Probability*, §§1 and 4](https://plato.stanford.edu/entries/logic-probability/), Stanford Encyclopedia of Philosophy, 2023 HTML | `0d0c542e881985347534c2596a2ccbbfb9a4090a2d7fe7ef06c34a014663173d` |

Build the public headers and their proof modules with

```sh
lake build --wfail +Silmaril.Logic.ManyValuedCatalogue.Thms +Silmaril.Logic.ManyValuedCatalogue.Discrete.Thms
make check CHECK_TARGETS='+Silmaril.Logic.ManyValuedCatalogue.Thms +Silmaril.Logic.ManyValuedCatalogue.Discrete.Thms'
```
