module

public import Silmaril.Project.Defs
public import Silmaril.Project.Registry.Consequence.Defs
public import Silmaril.Logic.Consequence.Defs
public import Silmaril.Logic.Consequence.Gentzen.Defs

/-!
# Standard problem shapes: consequence systems

The questions a project asks about its consequence systems (`S : Silmaril.Consequence.System
Ax C`, that is `Ax → C → Prop`, `S Γ φ` read "`Γ ⊢ φ`", registered with
`silmaril consequence_system`), as problems over arguments. Each
shape keeps the context `Γ` and the conclusion `φ` as its last arguments, so an instance that
fixes the systems (and maps, and `ff`) is a problem over contexts and conclusions, and its SZS
statuses are the usual questions. `Silmaril.Project.Shapes.Consequence.Thms` proves each reading
below for exactly the binders that remain, in order (so for an empty type of contexts, THM and
UNS of `derives S` both hold, and SAT and CSA both fail — nothing is assumed nonempty):

| name | statement | THM | SAT | UNS | CSA |
|---|---|---|---|---|---|
| `silmaril.shapes.consequence.derives` | `Derives S Γ φ`: `S Γ φ` | `S` is universal | `S` derives something | `S` is empty | `S` is not universal |
| `silmaril.shapes.consequence.context_universal` | `ContextUniversal S Γ`: `∀ φ, S Γ φ` | every context derives every conclusion | some context derives every conclusion | no context derives every conclusion | some context does not derive every conclusion |
| `silmaril.shapes.consequence.derives_bottom` | `DerivesBottom S ff Γ`: `S Γ ff` | every context derives `ff` | some context derives `ff` | no context derives `ff` | some context does not derive `ff` |
| `silmaril.shapes.consequence.sound_at` | `SoundAt S T Γ φ`: `S Γ φ → T Γ φ` | `S` is sound for `T`: `S ≤ T` | | | a counterexample: `S Γ φ`, not `T Γ φ` |
| `silmaril.shapes.consequence.complete_at` | `CompleteAt S T Γ φ`: `T Γ φ → S Γ φ` | `S` is complete for `T`: `T ≤ S` | | | a counterexample: `T Γ φ`, not `S Γ φ` |
| `silmaril.shapes.consequence.complete_within_at` | `CompleteWithinAt S T μ b Γ φ`: `μ Γ φ ≤ b → T Γ φ → S Γ φ` | `S` is complete for `T` on the pairs with `μ Γ φ ≤ b` | | | a counterexample within the bound |
| `silmaril.shapes.consequence.translates_at` | `TranslatesAt S T f g Γ φ`: `S Γ φ → T (f Γ) (g φ)` | `(f, g)` preserves consequence | | | a consequence it does not preserve |
| `silmaril.shapes.consequence.reflects_at` | `ReflectsAt S T f g Γ φ`: `T (f Γ) (g φ) → S Γ φ` | `(f, g)` reflects consequence (conservativity) | | | a translated consequence whose source is not one |

`silmaril.shapes.consequence.gentzen_closed rs S` (`Gentzen.Closed rs S`, closed once `rs` and
`S` are fixed) certifies that a sequent relation `S : Gentzen.Seq C` is closed under the rule
profile `rs` (`Gentzen.defaultRules`, `withWeakening W`, …): THM certified, UNS (a closed
refutation) not closed. A list-to-list system is only a *raw* sequent relation until such a
problem is proved.

Fixing `Γ` too (`derives S (Γ := …)`) asks about one context: THM says `Γ` derives every
conclusion (`Γ` is **context-universal**), CSA that some conclusion is not derived. Fixing `φ`
as well is the **member judgment** `Γ ⊢ φ`: THM true, CSA false (at arity 0 an UNS answer is
a CSA), no answer unknown.

**Three different properties, never one "inconsistent".** *Universal* (`derives` THM) says
every context derives every conclusion; *context-universal* (`context_universal` with `Γ`
fixed, or `derives` with `Γ` fixed, THM) says one context does; *derives `ff`*
(`derives_bottom`, for a chosen conclusion `ff`) says a context derives that conclusion. They
coincide only under structural rules a system may not have (for instance, `ff ⊢ φ` for every
`φ` and cut). The explorer and these docs name each one, never an unqualified
"inconsistent".

**Directions.** `sound_at S T` is `S ≤ T` (every consequence of `S` is one of `T`): a derivation
system `S` is sound for its target `T`; `complete_at S T` is the converse inclusion. A CSA
answer whose proof is a literal `⟨Γ, φ, h⟩` records `Γ` and `φ` as its witnesses.

**Unknown is not false.** Derivability is undecidable in general; a problem with no answer is
unknown, and only a Lean proof changes that.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.Consequence

open Silmaril.Consequence (System)

/-- **`Γ ⊢ φ` in `S`.** -/
@[problem "silmaril.shapes.consequence.derives" (title := "A context derives a conclusion")]
def Derives {Ax C : Type} (S : System Ax C) (Γ : Ax) (φ : C) : Prop := S Γ φ

/-- **`Γ` derives every conclusion in `S`.** -/
@[problem "silmaril.shapes.consequence.context_universal"
  (title := "A context derives every conclusion")]
def ContextUniversal {Ax C : Type} (S : System Ax C) (Γ : Ax) : Prop := ∀ φ, S Γ φ

/-- **`Γ` derives the chosen conclusion `ff` in `S`.** -/
@[problem "silmaril.shapes.consequence.derives_bottom"
  (title := "A context derives a chosen conclusion ff")]
def DerivesBottom {Ax C : Type} (S : System Ax C) (ff : C) (Γ : Ax) : Prop := S Γ ff

/-- **Soundness at `(Γ, φ)`**: if `Γ ⊢ φ` in `S` then in `T`. -/
@[problem "silmaril.shapes.consequence.sound_at" (title := "A system is sound for another")]
def SoundAt {Ax C : Type} (S T : System Ax C) (Γ : Ax) (φ : C) : Prop := S Γ φ → T Γ φ

/-- **Completeness at `(Γ, φ)`**: if `Γ ⊢ φ` in `T` then in `S`. -/
@[problem "silmaril.shapes.consequence.complete_at" (title := "A system is complete for another")]
def CompleteAt {Ax C : Type} (S T : System Ax C) (Γ : Ax) (φ : C) : Prop := T Γ φ → S Γ φ

/-- **Bounded completeness at `(Γ, φ)`**: if `μ Γ φ ≤ b` and `Γ ⊢ φ` in `T`, then in `S`. -/
@[problem "silmaril.shapes.consequence.complete_within_at"
  (title := "A system is complete for another within a measure bound")]
def CompleteWithinAt {Ax C : Type} (S T : System Ax C) (μ : Ax → C → ℕ) (b : ℕ) (Γ : Ax) (φ : C) :
    Prop := μ Γ φ ≤ b → T Γ φ → S Γ φ

/-- **A sequent relation is closed under a Gentzen rule profile.** -/
@[problem "silmaril.shapes.consequence.gentzen_closed"
  (title := "A sequent relation is closed under a Gentzen rule profile")]
def GentzenClosed {C : Type} (rs : Silmaril.Consequence.Gentzen.Rules C)
    (S : Silmaril.Consequence.Gentzen.Seq C) : Prop :=
  Silmaril.Consequence.Gentzen.Closed rs S

/-- **A translation preserves `Γ ⊢ φ`**: from `S` to `T` along `f` on contexts and `g` on
conclusions. -/
@[problem "silmaril.shapes.consequence.translates_at"
  (title := "A translation preserves consequence")]
def TranslatesAt {Ax C Bx D : Type} (S : System Ax C) (T : System Bx D) (f : Ax → Bx)
    (g : C → D) (Γ : Ax) (φ : C) : Prop := S Γ φ → T (f Γ) (g φ)

/-- **A translation reflects `Γ ⊢ φ`**: if the translation of `Γ ⊢ φ` holds in `T`, then
`Γ ⊢ φ` holds in `S`. -/
@[problem "silmaril.shapes.consequence.reflects_at"
  (title := "A translation reflects consequence")]
def ReflectsAt {Ax C Bx D : Type} (S : System Ax C) (T : System Bx D) (f : Ax → Bx)
    (g : C → D) (Γ : Ax) (φ : C) : Prop := T (f Γ) (g φ) → S Γ φ

end Silmaril.Project.Shapes.Consequence
