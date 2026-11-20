module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Defs
public import Silmaril.Semantics.Accept.Mixed.Stream.Defs

/-!
# Streaming parsers that build their trees: stateful export specifications

An export specification `Silmaril.Wasm.Logic.Strategy.ISpec` constrains each export answer on
its own. A streaming parser (`append(v : i64)` and `done() -> i32`) answers `done()` with a tree
built from the values appended **since the last `done`**, which the module keeps in its store
(globals, memory). Its specification needs that history, so it is stated with a **ghost state**
`g : G` (here the pending buffer) and a store invariant `inv g s` relating the module's store
to it.

## Stateful specifications

`SSpec I G` (for an instance `I`, ghost states `G`):

* `inv g s`: the store `s` (between export calls) represents the ghost state `g`;
* `post g f v`: the guarantee on the answer `v` to the export call `f` made in ghost state `g`;
* `next g f v`: the ghost state after that answer.

`sexportSpec I S j` is the Hoare specification of export `j` (`Silmaril.Wasm.Logic.Hoare.FSpec`):
from a store representing some ghost state, on typed arguments, every outcome that is an answer
`v` meets `post g f v` and ends in a store representing `next g f v`, for every ghost state `g`
the initial store represents. `SGameSat P I Ii S`: every export meets it in the every-run logic
under the most general environment of the import specification `Ii` (as
`Silmaril.Wasm.Logic.GameLink.GameSat`, which is the case of a one-point ghost).

`gval s a` reads the value of the global at address `a` (module state kept in globals).

`SAG Ii S g p`: the play `p`, read from the ghost state `g`, is assume/guarantee correct: every
Proponent move is allowed (import questions by `Ii.pre`, export answers by `post` in the current
ghost state) as long as Opponent's import answers were allowed by `Ii.post`; the ghost state
moves by `next` at every export answer. Export calls are not re-entrant, so the ghost state at an
answer is the one of its call.

## The streaming parsing specification

For parsing exports `pix` and a parsing policy `ppol`, the ghost state is the **pending append
buffer** (`List V`):

* `streamNext pix ppol g f v`: the buffer after the answer, by
  `Silmaril.Accept.Mixed.accStep` on the decoded parsing event (`parseDec`), unchanged when the
  answer decodes to no event (a trap, an exception, another export);
* `streamSSpec pix ppol ρ R Inv`: `inv := Inv`, `next := streamNext`, and the guarantee: a
  decoded event returning, from a parsing state whose buffer is `g`, a non-sentinel handle `h` for
  the input `w` has `(w, x) ∈ R` for `ρ h = some x`. For `done() -> h` the input is `g` itself,
  so the tree is constrained by the values appended since the last `done`.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Stream

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed
  Silmaril.Wasm.Game.HandleAccept.Parsing
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid)
open Silmaril.Wasm.Logic.GameLink (gameHost)

/-! ## Stateful specifications -/

/-- **A stateful export specification** with ghost states `G`. -/
structure SSpec (I : ScalarInstance) (G : Type) where
  /-- The store represents the ghost state. -/
  inv : G → Store Nat → Prop
  /-- The guarantee on an answer, in the ghost state of its call. -/
  post : G → (f : I.F.Op) → I.F.Ar f → Prop
  /-- The ghost state after an answer. -/
  next : G → (f : I.F.Op) → I.F.Ar f → G

variable {I : ScalarInstance} {G : Type}

/-- The Hoare specification of export `j` for the stateful specification `S`. -/
def sexportSpec (I : ScalarInstance) (S : SSpec I G) (j : Fin I.exports.length) : FSpec Nat where
  pre s args := (∃ g, S.inv g s) ∧ List.Forall₂ ScalarType.HasVal (I.exports.get j).params args
  post s₀ args s' o := ∀ g, S.inv g s₀ →
    ∀ (ht : List.Forall₂ ScalarType.HasVal (I.exports.get j).params args)
      (v : Answer (I.exports.get j)), resultOutcome v.toResult = o →
      S.post g ⟨j, ⟨args, ht⟩⟩ v ∧ S.inv (S.next g ⟨j, ⟨args, ht⟩⟩ v) s'

/-- **The instance meets the stateful specification `S` under `Ii`** (partial correctness). -/
def SGameSat (P : Profile) (I : ScalarInstance) (Ii : ISpec I.E) (S : SSpec I G) : Prop :=
  ∀ j, FSpecValid P (gameHost I Ii) (I.addr j) (sexportSpec I S j)

/-- **Assume/guarantee correctness of a play read from the ghost state `g`.** -/
def SAG (Ii : ISpec I.E) (S : SSpec I G) : G → List (Move I.E I.F) → Prop
  | _, [] => True
  | g, .inl (.ask e) :: p => Ii.pre e ∧ SAG Ii S g p
  | g, .inl (.ans e v) :: p => Ii.post e v → SAG Ii S g p
  | g, .inr (.ask _) :: p => SAG Ii S g p
  | g, .inr (.ans f v) :: p => S.post g f v ∧ SAG Ii S (S.next g f v) p

/-- The value of the global at address `a` of a store. -/
def gval (s : Store Nat) (a : Nat) : Option Val := (s.globals[a]?).map (·.value)

/-! ## The streaming parsing specification -/

variable {V X : Type}

/-- The pending buffer after an export answer. -/
def streamNext (pix : ParseExports V) (ppol : PPolicy (BitVec 32)) (g : List V) (f : I.F.Op)
    (v : I.F.Ar f) : List V :=
  match parseDec pix f v with
  | some e => accStep ppol.doneClears g e
  | none => g

/-- **The streaming parsing specification** in the environment `ρ`, with the store invariant
`Inv` relating the module's store to the pending buffer. -/
def streamSSpec (pix : ParseExports V) (ppol : PPolicy (BitVec 32))
    (ρ : Env (BitVec 32) X) (R : Set (List V × X)) (Inv : List V → Store Nat → Prop) :
    SSpec I (List V) where
  inv := Inv
  post g f v := ∀ e, parseDec pix f v = some e → ∀ ps w h ps', ps.acc = g →
    Returns ppol ps e w h ps' → h ≠ ppol.sentinel → ∀ x, ρ h = some x → (w, x) ∈ R
  next := streamNext pix ppol

end Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
