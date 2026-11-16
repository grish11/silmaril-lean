# Consequence systems in a silmaril project

A project can name **consequence systems** — `Silmaril.Consequence.System Ax C`, relations
`S : Ax → C → Prop` from contexts to conclusions, `S Γ φ` read `Γ ⊢ φ`
(`Silmaril.Logic.Consequence.Defs`) — say how each was built, and ask the standard questions
about them as ordinary project problems, answered by Lean proofs. It reuses the registry's
problems, instances, answers and statuses (`@[answers "N" thm|sat|uns|csa]`); nothing here
adds a status or a tag.

| Piece | Where |
| --- | --- |
| Record kind `consequence_system` | `Silmaril.Project.Registry.Consequence.Defs` |
| Standard shapes `silmaril.shapes.consequence.*` | `Silmaril.Project.Shapes.Consequence.Defs`, readings in `….Thms` |
| Worked fixture (the self-test) | `examples/project/ProjectSelfTest/Consequence.lean` |
| Database tables | `tools/silmaril-project/src/project/schema/consequence.rs` |
| Explorer page | `tools/silmaril-project/src/project/explore/views/systems.js` (`#/systems`, `#/system/<name>`) |
| Browser test | `tools/silmaril-project/tests/explore/systems.mjs` |

## What a system is

`Ax` is any type of contexts — a finite list `C₁, …, Cₙ`, a finite set, a single formula — and
`C` any type of conclusions. **No structural rule is implicit**: a system is reflexive
(`φ ∈ Γ → Γ ⊢ φ`), monotone or closed under cut only when a proof says so. The registry checks
types only (`Ax → C → Prop`, universe-monomorphic); every property is a problem.

A **witness system** `W : Ax → C → Type` (a `WSystem`) gives a type of derivations of each
`Γ ⊢ φ`; it is registered through its erasure `WSystem.erase W` (`Nonempty (W Γ φ)`), so that a proof of `Γ ⊢ φ` is a
derivation and a refutation shows that no derivation exists.

## Registering systems

```lean
-- an existing definition (op := decl, the default)
silmaril consequence_system my.raw := My.raw (title := "One rule step") (source := some-bib-key)
-- the erasure of a witness system
silmaril consequence_system my.derivable := My.Deriv (op := erase)
-- constructions: Lean generates the definition
silmaril consequence_system my.both (op := union) (args := [my.raw, my.hyp])    -- my.raw ⊔ my.hyp
silmaril consequence_system my.checked (op := inter) (args := [my.derivable, my.entails])
silmaril consequence_system my.gap (op := diff) (args := [my.entails, my.derivable])
```

| `op` | fields | definition |
| --- | --- | --- |
| `decl` | `decl := S` | the existing `S : Ax → C → Prop` |
| `erase` | `decl := W` (`W : Ax → C → Type`) | `Silmaril.Consequence.WSystem.erase W`; `witness := W` is kept |
| `union`, `inter` | `args := [A, B, …]`, at least two | `A ⊔ B ⊔ …`, `A ⊓ B ⊓ …` (Mathlib's pointwise lattice) |
| `diff` | `args := [A, B]`, exactly two | `A \ B` |

The operands of a construction must have definitionally equal context types and conclusion
types (Lean checks this with `isDefEq`; the printed `contexts` and `conclusions` columns are
for reading only). There is no nullary union or intersection: register the empty or universal
system with `op := decl`. Lean fills `decl`, `contexts`, `conclusions` and `term` (the defining
constant as instance arguments print it, which is how the database relates problems to
systems). `title`, `doc` and `source` (a `references.bib` key) are kept as written.

## The standard problems

Each shape keeps the context `Γ` and the conclusion `φ` last; an instance fixes the systems
(and maps, and `ff`) and asks about what is left free. The readings are proved in
`Silmaril.Project.Shapes.Consequence.Thms` for exactly the binders that remain, in order;
nothing is assumed inhabited (over an empty type of contexts, `derives S` is THM and UNS at
once).

| shape | statement | THM | SAT | UNS | CSA |
| --- | --- | --- | --- | --- | --- |
| `derives S Γ φ` | `S Γ φ` | `S.Universal` (`S = ⊤`) | `S` derives something | `S` empty (`S = ⊥`) | `S` not universal |
| `context_universal S Γ` | `∀ φ, S Γ φ` | every context derives everything | some context is context-universal | none is | some context is not |
| `derives_bottom S ff Γ` | `S Γ ff` | every context derives `ff` | some context derives `ff` | no context derives `ff` | some context does not |
| `sound_at S T Γ φ` | `S Γ φ → T Γ φ` | `S.Sound T` (`S ≤ T`) | | | a counterexample |
| `complete_at S T Γ φ` | `T Γ φ → S Γ φ` | `S.Complete T` (`T ≤ S`) | | | a counterexample |
| `translates_at S T f g Γ φ` | `S Γ φ → T (f Γ) (g φ)` | `S ≤ T.pullback f g`: the translation preserves consequence | | | a consequence not preserved |
| `reflects_at S T f g Γ φ` | `T (f Γ) (g φ) → S Γ φ` | `T.pullback f g ≤ S`: the translation reflects consequence | | | a translated consequence not reflected |

(all named `silmaril.shapes.consequence.<shape>`; with `Γ` fixed, `context_universal` is
`S.ProvesAll Γ`, and `derives_bottom` is `S.ProvesFalse ff Γ`, its refutation
`S.ConsistentWrt ff Γ`.)

* Fixing `Γ` in `derives` asks about one context: THM says `Γ` derives every conclusion,
  CSA that some conclusion is not derived. Fixing `Γ` and `φ` is the **member judgment**
  `Γ ⊢ φ`: THM true; a refutation is stored as UNS (false), so a closed negative example
  expects `UNS`.
* **Three properties, not one "inconsistency".** *Universal*, *context-universal* and
  *derives `ff`* coincide only under structural rules a system may not have; the shapes, the
  explorer and these docs always name which one is meant
  (`derivesBottom_not_contextUniversal`, `contextUniversal_not_universal`).
* **Soundness is directional**: `sound_at S T` asks whether the derivation system `S` is
  sound for its target `T`; completeness is `complete_at S T`. A CSA proof written
  `⟨Γ, φ, h⟩` records `Γ` and `φ` as the witness, so a counterexample is kept with the answer.
* **Expected outcomes**: `(expect := CSA)` (or `UNS` when closed) marks an expected negative
  result, which the explorer's shared status badge shows as a match (✓), not a failure.
* **Unknown is not false.** A problem with no answer is unknown; only a Lean proof changes it.

## The self-test example

`examples/project/ProjectSelfTest/Consequence.lean` has four sentences `p q r ff`, finite
lists as contexts, and the rules `p ⇒ q`, `q ⇒ r`:

| system | construction | what the problems show |
| --- | --- | --- |
| `raw` | `decl`: one rule step from a one-element context | `p ⊢ p` fails (no reflexivity); sound for `derivable` |
| `hyp`, `raw_or_hyp` | `decl`; `union` | one step does not chain: not complete for `derivable` (`p ⊢ r`) |
| `derivable` | `erase` of the derivation type `Deriv` | `p ⊢ r` holds, `r ⊢ p` fails; sound for `entails`, **not complete** (`ff ⊢ p`); `ff` is not context-universal, some contexts derive `ff` and some do not; a translation preserves but does not reflect it |
| `entails` | `decl`: truth in every model of the rules where `ff` is false | `ff` is context-universal |
| `gap`, `checked` | `diff`, `inter` | something is entailed but not derivable; `checked` is complete for `derivable` (by soundness) |
| `empty` | `decl` | derives nothing (UNS) |

`examples/project/ProjectSelfTest/Consequence/Gentzen.lean` registers the literal sequents of
`Silmaril.Consequence.Gentzen.Examples` (`Γ ⊢ Δ` over lists of literals), answered by that
module's theorems: validity and the complementary-pair UNSAT test are sound and complete for
each other; `p ⊢ q, p` is valid and `p ⊢ q` is not; a test bounded to three literals and its
closure under the default Gentzen rules are sound for validity, while the bounded test is
**not complete for its own closure** (the cut of `p, r ⊢ p` and `p, q ⊢ p` is the kept
counterexample); `p ⊢ r` holds in the cut closure of `p ⊢ q, q ⊢ r` and not in the raw
sequents. Closures are registered as `op := decl` of the library's `Derives rules S`.

## Database and explorer

`sil project sqlite` writes `consequence_systems` (name, op, decl, term, contexts,
conclusions, witness, provenance), `consequence_operands`, `consequence_shape_roles` and the
view `consequence_problems` (each instance of a consequence shape with the systems its
arguments name, role `S` or `T`, expected status, summary and verdict). Systems are matched by
`term`, the defining constant exactly as Lean prints an instance argument, not by `decl`: a
generated system `silmaril.x` prints as `«silmaril».x` (`silmaril` is a keyword), and the
self-test's generated systems are such names. A database written by an older `sil project` has
none of these tables; the explorer then shows a notice instead of the Systems page. The explorer's
**Systems** page lists the systems and what each status of each shape means; a system's page
shows its definition (with a source link when the page has sources), its construction and
every problem about it with the outcome, the reading for the arguments left free, and the
Lean answers with their witnesses. Browsing never runs anything.

The browser test runs on a built site (`make project-check` writes the database;
`sil project explore` the page):

```sh
node tools/silmaril-project/tests/explore/systems.mjs SITE_DIR [SHOTS_DIR]
```

## Not yet here

Closure operators and structural rules (reflexivity, monotonicity, cut; the core's
`Silmaril.Consequence.Structural`) as shapes or `op := closure`, and translations between
systems as records, are planned; today a translation is the pair of maps given to
`translates_at`/`reflects_at`.
