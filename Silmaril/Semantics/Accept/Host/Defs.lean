module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Image

/-!
# Host models: acceptance through an environment that answers calls

Handle-based acceptance APIs (`Silmaril.Semantics.Accept.Handle`) and input/parsing sessions
(`Silmaril.Semantics.Accept.Parse`) share one shape. A module produces **event traces**
`List E`: every call it makes to the environment, with the answer it observed. A *host model*
says which answers the environment may give, and which values a call makes the module accept:

* `Host E X S`: states `S`, an initial state, and a response relation
  `resp s e s' A`: in state `s` the environment allows the event `e` (the call with its recorded
  answer), moving to `s'`; the event makes the module accept every value of `A : Set X`.
* `Run h s t s' A`: the trace `t` is allowed from `s`, ending in `s'` and accepting `A` in total.
* `accepts h t`: the values accepted by some run of `t` from the initial state;
  `lang h T := ⋃ t ∈ T, accepts h t` for a set `T` of module traces.
* `langOver Hs T := ⋃ i, lang (Hs i) T`: a union over an indexed family of hosts, for
  quantifying explicitly over environments (fixed handle environments, for instance).

**Nondeterminism, restriction and traps are different things here.** A response relation with
several answers is a nondeterministic environment; a smaller response relation is a *restricted*
environment and accepts less (`Sim`); a call with no response (no `resp` at all) is a host trap:
nothing after it is allowed. A trace may stop anywhere, so a trace that ends is not a trap
of the host but of the module, or a cut-off; acceptance is observed at the event that causes it
(a *may* property of finite prefixes).

**Simulation.** `Sim h₁ h₂ f R` relates states so that every response of `h₁` to `e` is matched
by a response of `h₂` to `f e` accepting at least as much. It gives
`lang h₁ T ⊆ lang h₂ (List.map f '' T)` (`Thms`); with `f = id` it compares two environments on
the same module.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w w'

/-- **A host model** for event type `E` and accepted values `X`, with states `S`. -/
structure Host (E : Type u) (X : Type v) (S : Type w) where
  /-- The initial state. -/
  init : S
  /-- `resp s e s' A`: from `s` the event `e` is allowed, reaching `s'` and accepting `A`. -/
  resp : S → E → S → Set X → Prop

namespace Host

variable {E : Type u} {X : Type v} {S : Type w}

/-- **Runs** of a host along a trace, with the accumulated accepted values. -/
inductive Run (h : Host E X S) : S → List E → S → Set X → Prop where
  | nil (s : S) : Run h s [] s ∅
  | cons {s s₁ s₂ : S} {e : E} {es : List E} {A B : Set X} :
      h.resp s e s₁ A → Run h s₁ es s₂ B → Run h s (e :: es) s₂ (A ∪ B)

/-- The values a trace makes the module accept, in some run from the initial state. -/
def accepts (h : Host E X S) (t : List E) : Set X :=
  {x | ∃ s A, h.Run h.init t s A ∧ x ∈ A}

/-- **The language of a set of module traces** under the host model. -/
def lang (h : Host E X S) (T : Set (List E)) : Set X :=
  ⋃ t ∈ T, h.accepts t

/-- The traces the host allows from the initial state. -/
def allowed (h : Host E X S) : Set (List E) :=
  {t | ∃ s A, h.Run h.init t s A}

/-- **A simulation** of `h₁` by `h₂` along the event map `f`. -/
structure Sim {E' : Type u} {S' : Type w'} (h₁ : Host E X S) (h₂ : Host E' X S') (f : E → E')
    (R : S → S' → Prop) : Prop where
  init : R h₁.init h₂.init
  step : ∀ {s₁ s₂ e s₁' A}, R s₁ s₂ → h₁.resp s₁ e s₁' A →
    ∃ s₂' B, h₂.resp s₂ (f e) s₂' B ∧ R s₁' s₂' ∧ A ⊆ B

end Host

/-- **The language over a family of hosts**: accepted under some environment of the family. -/
def langOver {ι : Sort*} {E : Type u} {X : Type v} {S : Type w} (Hs : ι → Host E X S)
    (T : Set (List E)) : Set X :=
  ⋃ i, (Hs i).lang T

end Silmaril.Accept
