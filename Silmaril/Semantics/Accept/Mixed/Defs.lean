module

public import Silmaril.Semantics.Accept.Parse.Defs

/-!
# Mixed sessions: a writer module that answers parsing exports

A *parser that builds its trees* talks to its environment on two sides at once:

* through **writer imports** (`Silmaril.Accept.Handle.WEv`: `write op args r`, `accept h`, …,
  and the export-call boundary `enter`), answered by the writer response relation
  `Silmaril.Accept.Handle.WStep` (store semantics, or restricted to a fixed environment);
* through **parsing exports** (`Silmaril.Accept.Parse.PEv`: `parse v h`, `append v`, `done h`,
  `feed chunk`, `finish used h`, `reset`), answered by `Silmaril.Accept.Parse.PStep`.

`MEv Op V H` has both kinds of events (`.w e`, `.p e`). The point of the combination is **where a
returned handle is resolved**: the parsing response of a mixed session resolves it in the
**current writer store** (`MStep.p`), the meaning of every handle the module has obtained from a
successful write so far, instead of an environment chosen up front
(`Silmaril.Accept.Parse.parseRel … Envs`). The input/tree relation `mixedRel` is therefore about
trees the module **actually constructed**: a handle resolves only if some earlier write of the
same trace returned it (`Thms.mixedRel_constructed`).

## The state and the response relation

The state `MState` pairs the writer state (`WState`: store, batch, writer phase) with the
parsing state (`PState`: append buffer, chunk buffer, parsing phase).

* `MStep.w`: a writer event steps the writer component by `WStep W pol fix` and leaves the
  parsing state. It relates **no pair**, unless the writer enters undefined behaviour
  (phase `chaos`), which is the top element: every pair (`chaosPairs`).
* `MStep.p`: a parsing event is answered only while the writer is `live` (not after a call-local
  trap of the current export call, which aborts it before it returns; not after a session abort),
  by `PStep pol' σ` where `σ` is the **current store**. Its accepted pairs are those of `PStep`.
* `MStep.pChaos`: once the writer is in `chaos`, every parsing event is allowed and relates every
  pair.

Policies are the two components' own: the writer `Policy` (sentinel, interning, call-local
trap `callTrap` by default, …) and the parsing `PPolicy` (sentinel of returned handles,
`onBadHandle` for a returned handle the store does not resolve, …). The two sentinels are
independent (a writer may fail with `0` and a parser answer `-1`).

## Relations

* `mixedRel W pol ppol T`: store semantics (`fix = none`): writes are answered by any fresh (or
  interned) handle; a returned handle denotes whatever the store says at the time it is returned.
* `mixedFixedRel W pol ppol Envs T`: over fixed environments `ρ ∈ Envs` (`fix = some ρ`), as
  `Silmaril.Accept.Handle.fixedLang`: every successful write must agree with `ρ`, so the store
  stays below `ρ` and a returned handle resolves, if at all, to its meaning in `ρ`.

## Projections

`parseEvents t` keeps the parsing events of a mixed trace (the parsing session the module
exposes); `writeEvents t` keeps the writer events. `reachStores` are the final writer stores of
runs of a set of traces: the environments against which a mixed relation is compared with a
plain parsing relation (`Thms.mixedRel_subset_parseRel`).

**Assume/guarantee per trace.** `WritesAgree W s σ t`: every write of `t` failed with the
sentinel `s` or denotes in `σ` the tree it builds in `σ` (`WriteAgrees`, the per-event form of
an import specification); `ReturnsIn ppol σ R t`: every non-sentinel handle returned in `t`
denotes in `σ` a tree related by `R` to its input (an export specification). A trace class in
which the second follows from the first for every `σ` has its mixed relation in `R`
(`Thms.mixedRel_subset_of_AG`): the import side ties handles to trees, so the export side can
constrain the tree.

`NoWriterUB pol fix`: the writer never enters undefined behaviour (`fix` fixed, or neither
invalid writes nor invalid accepts are `ub`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Accept.Mixed

open Silmaril.Accept.Handle Silmaril.Accept.Parse

universe u

/-- **Events of a mixed session**: writer events (imports, export-call boundaries) and parsing
events (export answers). -/
inductive MEv (Op V H : Type u) where
  | w (e : WEv Op H)
  | p (e : PEv V H)

/-- The state of a mixed session: the writer state and the parsing state. -/
structure MState (V H X : Type u) where
  ws : WState H X
  ps : PState V

/-- The initial state. -/
def MState.init {V H X : Type u} : MState V H X := ⟨WState.init, PState.init⟩

/-- Every pair when the phase is `chaos` (undefined behaviour of the writer), none otherwise. -/
def chaosPairs {V X : Type u} (ph : Phase) : Set (List V × X) := {_q | ph = .chaos}

variable {Op V H X : Type u}

/-- **The mixed response relation** (see the module docstring): writer events by `WStep`,
parsing events by `PStep` in the **current store**, while the writer is live. -/
inductive MStep [DecidableEq H] (W : Writer Op X) (pol : Policy H) (ppol : PPolicy H)
    (fix : Option (Env H X)) : MState V H X → MEv Op V H → MState V H X → Set (List V × X) →
    Prop where
  | w {ws ws' : WState H X} {ps : PState V} {e : WEv Op H} {A : Set X} :
      WStep W pol fix ws e ws' A →
        MStep W pol ppol fix ⟨ws, ps⟩ (.w e) ⟨ws', ps⟩ (chaosPairs ws'.phase)
  | p {ws : WState H X} {ps ps' : PState V} {e : PEv V H} {A : Set (List V × X)} :
      ws.phase = .live → PStep ppol ws.store ps e ps' A →
      MStep W pol ppol fix ⟨ws, ps⟩ (.p e) ⟨ws, ps'⟩ A
  | pChaos {ws : WState H X} {ps : PState V} {e : PEv V H} :
      ws.phase = .chaos → MStep W pol ppol fix ⟨ws, ps⟩ (.p e) ⟨ws, ps⟩ Set.univ

/-- **The mixed host**: `fix = none` is the store semantics; `fix = some ρ` restricts writes to
the fixed environment `ρ`. -/
def mixed [DecidableEq H] (W : Writer Op X) (pol : Policy H) (ppol : PPolicy H)
    (fix : Option (Env H X) := none) : Host (MEv Op V H) (List V × X) (MState V H X) :=
  ⟨MState.init, MStep W pol ppol fix⟩

/-- **The input/tree relation of a mixed module** (store semantics): returned handles are
resolved in the store of the trees the module has constructed. -/
def mixedRel [DecidableEq H] (W : Writer Op X) (pol : Policy H) (ppol : PPolicy H)
    (T : Set (List (MEv Op V H))) : Set (List V × X) :=
  (mixed W pol ppol).lang T

/-- **The input/tree relation over fixed environments**: some `ρ ∈ Envs` agrees with every
successful write; returned handles are resolved in the store, which stays below `ρ`. -/
def mixedFixedRel [DecidableEq H] (W : Writer Op X) (pol : Policy H) (ppol : PPolicy H)
    (Envs : Set (Env H X)) (T : Set (List (MEv Op V H))) : Set (List V × X) :=
  langOver (fun ρ : Envs => mixed W pol ppol (some ρ.1)) T

/-- The parsing events of a mixed trace. -/
def parseEvents : List (MEv Op V H) → List (PEv V H)
  | [] => []
  | .p e :: t => e :: parseEvents t
  | .w _ :: t => parseEvents t

/-- The writer events of a mixed trace. -/
def writeEvents : List (MEv Op V H) → List (WEv Op H)
  | [] => []
  | .w e :: t => e :: writeEvents t
  | .p _ :: t => writeEvents t

/-- The final writer stores of the runs of a set of traces. -/
def reachStores [DecidableEq H] (W : Writer Op X) (pol : Policy H) (ppol : PPolicy H)
    (T : Set (List (MEv Op V H))) : Set (Env H X) :=
  {σ | ∃ t ∈ T, ∃ s A, (mixed W pol ppol).Run MState.init t s A ∧ σ = s.ws.store}

/-- The writer never enters undefined behaviour: a fixed environment, or no `ub` policy. -/
def NoWriterUB (pol : Policy H) (fix : Option (Env H X)) : Prop :=
  fix.isSome ∨ (pol.onWrite ≠ .ub ∧ pol.onAccept ≠ .ub)

/-- A write answered by `r` **agrees with** `σ` (or failed with the sentinel `s`): `r` denotes in
`σ` the tree the call builds in `σ`. This is the per-event form of the writer import
specification of a fixed environment. -/
def WriteAgrees (W : Writer Op X) (s : Option H) (σ : Env H X) (op : Op) (args : List H) (r : H) :
    Prop :=
  s = some r ∨ ∃ t, W.built σ op args = some t ∧ σ r = some t

/-- **The writes of a trace agree with `σ`**: the per-trace form of the writer import
specification of the environment `σ`. -/
def WritesAgree (W : Writer Op X) (s : Option H) (σ : Env H X) (t : List (MEv Op V H)) : Prop :=
  ∀ op args r, MEv.w (.write op args r) ∈ t → WriteAgrees W s σ op args r

/-- **The returns of a trace are related in `σ`**: every parsing event of `t` returning, for the
input `w`, a non-sentinel handle `h` denoting `x` in `σ` relates `(w, x) ∈ R`. The input is the
one `Returns` gives from *any* parsing state: exactly `[v]` for `parse v h`, every possible
buffer for `done` and `finish`. -/
def ReturnsIn (ppol : PPolicy H) (σ : Env H X) (R : Set (List V × X)) (t : List (MEv Op V H)) :
    Prop :=
  ∀ e, MEv.p e ∈ t → ∀ ps w h ps', Returns ppol ps e w h ps' → h ≠ ppol.sentinel →
    ∀ x, σ h = some x → (w, x) ∈ R

end Silmaril.Accept.Mixed
