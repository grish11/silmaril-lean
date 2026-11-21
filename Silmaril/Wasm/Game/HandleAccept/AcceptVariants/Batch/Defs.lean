module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost.Defs

/-!
# Batches through instance plays: import-level ghost state

The store specification `storeISpec` of `Silmaril.Wasm.Game.HandleAccept.AcceptVariants`
constrains each import call on its own, so it bounds `accept_batch(keep ≠ 0)` only by the
constructed set: it cannot see which trees were built since the previous batch. This topic
threads a **ghost state** through the import calls of an instance play, moved at every import
question and every import answer, so that a precondition may depend on the history of the
session. For the writer, the ghost is **the current batch** (in a fixed environment `ρ`).

## Ghost import specifications

`GISpec E G`, over an import interface `E` and ghost states `G`:

* `pre g e`: the guarantee at the question `e`, in the ghost `g` before it;
* `post g e v`: the assumption on its answer `v`, in the ghost `g` after the question;
* `ask g e`: the ghost after the question;
* `next g e v`: the ghost after the answer.

`GAG Gi g p`: the play `p`, read from the ghost `g`, is assume/guarantee correct: every import
question meets `pre` in the current ghost; every import answer is to a question that met `pre`
(in the ghost before it) and, if it meets `post`, the rest of the play is correct from the moved
ghost. Export moves do not move the ghost.

## The program-logic obligation

As in `Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost`, the ghost lives in the **host code** of
the store of the specification world: `gStore g s` is the store `s` with every host function
`k` carrying the code `(k, g)`, nothing else changed.

* `ghostImportSpec I Gi k`: in a store `gStore g sR`, the call of import `k` with `args` is
  allowed when the arguments form a question `e` with `Gi.pre g e`; it answers some `v` with
  `Gi.post (Gi.ask g e) e v`, in the store `gStore (Gi.next (Gi.ask g e) e v) sR` (the
  environment does not write the store).
* `ghostHost I Gi`: the most general environment meeting it (`Open.specHost Prod.fst`).
* `ghostExportSpec I Inv j`: from a store `gStore g sR` with `Inv g sR`, on typed arguments,
  every outcome ends in a store `gStore g' sR'` with `Inv g' sR'`.
* `GhostGameSat P I Gi Inv`: every export meets `ghostExportSpec` under `ghostHost`.

## The batch specification

`batchGhost W ρ g ev` is the ghost after the writer event `ev`: an `acceptBatch` starts an
empty batch, a write adds the tree it builds in `ρ` (if any), other events keep it.
`batchGSpec W s dAsk dAns ρ L C` (ghost `Set X`, the current batch) has the guarantees of
`storeISpec` (accepts of `L`, writes building trees of `C`, `accept_all()` only when `C ⊆ L`),
except that `accept_batch(keep ≠ 0)` is only asked when **the current batch** is included in
`L`; the assumption is the write guarantee of `storeISpec`; `ask` and `next` move the ghost by
`batchGhost` on the decoded question and answer.

`keptL`: the trees of the kept batch of `batchAccept`, `nil` and the one-element lists of words.

New definitions (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost (gStore)
open Silmaril.Wasm.Logic.Strategy (ISpec resultOutcome)
open Silmaril.Wasm.Logic.Hoare (Ctx FSpec FSpecValid)

/-! ## Ghost import specifications -/

/-- **A ghost import specification** over the interface `E` with ghost states `G`. -/
structure GISpec (E : Sig.{0}) (G : Type) where
  /-- The guarantee at a question, in the ghost before it. -/
  pre : G → E.Op → Prop
  /-- The assumption on an answer, in the ghost after its question. -/
  post : G → (e : E.Op) → E.Ar e → Prop
  /-- The ghost after a question. -/
  ask : G → E.Op → G
  /-- The ghost after an answer. -/
  next : G → (e : E.Op) → E.Ar e → G

variable {E F : Sig.{0}} {G : Type}

/-- **Assume/guarantee correctness of a play read from the ghost `g`.** -/
def GAG (Gi : GISpec E G) : G → List (Move E F) → Prop
  | _, [] => True
  | g, .inl (.ask e) :: p => Gi.pre g e ∧ GAG Gi (Gi.ask g e) p
  | g, .inl (.ans e v) :: p =>
      (∃ g₀, g = Gi.ask g₀ e ∧ Gi.pre g₀ e) ∧ (Gi.post g e v → GAG Gi (Gi.next g e v) p)
  | g, .inr _ :: p => GAG Gi g p

/-! ## The program-logic obligation -/

section Logic

variable (I : ScalarInstance)

/-- **The specification of import `k`** under a ghost import specification. -/
def ghostImportSpec (Gi : GISpec I.E G) (k : Nat) : FSpec (Nat × G) where
  pre s args := ∃ g sR, s = gStore g sR ∧ ∃ e, I.importOp? k args = some e ∧ Gi.pre g e
  post s args s' o := ∃ g sR, s = gStore g sR ∧ ∀ e, I.importOp? k args = some e →
    ∃ v : I.E.Ar e, Gi.post (Gi.ask g e) e v ∧
      resultOutcome (Answer.toResult (ft := I.imports.get e.1) v) = o ∧
      s' = gStore (Gi.next (Gi.ask g e) e v) sR

/-- The import specifications, indexed by host code. -/
def ghostCtx (Gi : GISpec I.E G) : Ctx (Nat × G) := fun k => some (ghostImportSpec I Gi k)

/-- **The most general environment meeting a ghost import specification**: host code `(k, g)` is
import `k` called in the ghost `g`. -/
def ghostHost (Gi : GISpec I.E G) : Silmaril.Wasm.Execution.Core.HostSemantics (Nat × G) :=
  Silmaril.Wasm.Logic.Open.specHost Prod.fst (ghostCtx I Gi)

/-- The specification of export `j` for the ghost store invariant `Inv`. -/
def ghostExportSpec (Inv : G → Store Nat → Prop) (j : Fin I.exports.length) :
    FSpec (Nat × G) where
  pre s args := ∃ g sR, s = gStore g sR ∧ Inv g sR ∧
    List.Forall₂ ScalarType.HasVal (I.exports.get j).params args
  post _ _ s' _ := ∀ g sR, s' = gStore g sR → Inv g sR

end Logic

/-- **The instance meets the ghost import specification `Gi`** with the ghost store invariant
`Inv` (partial correctness). -/
def GhostGameSat (P : Profile) (I : ScalarInstance) (Gi : GISpec I.E G)
    (Inv : G → Store Nat → Prop) : Prop :=
  ∀ j, FSpecValid P (ghostHost I Gi) (I.addr j) (ghostExportSpec I Inv j)

/-! ## The batch specification -/

variable {Op X : Type}

/-- The current batch after the writer event `ev`, trees read in `ρ`. -/
def batchGhost (W : Writer Op X) (ρ : Silmaril.Accept.Handle.Env (BitVec 32) X) (g : Set X) :
    WEv Op (BitVec 32) → Set X
  | .acceptBatch _ => ∅
  | .write op args _ => g ∪ {t | W.built ρ op args = some t}
  | _ => g

/-- **The batch specification** in the fixed environment `ρ`, for the sentinel `s`, accepted
language `L` and constructed-set bound `C`, with the current batch as ghost. -/
def batchGSpec (W : Writer Op X) (s : Option (BitVec 32))
    (dAsk : E.Op → Option (WEv Op (BitVec 32)))
    (dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32)))
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) X) (L C : Set X) : GISpec E (Set X) where
  pre g e := (∀ h, dAsk e = some (.accept h) → ∀ t, ρ h = some t → t ∈ L) ∧
    (∀ v h b, dAns e v = some (.acceptErr h b) → ∀ t, ρ h = some t → t ∈ L) ∧
    (∀ v op args r, dAns e v = some (.write op args r) → ∀ t, W.built ρ op args = some t →
      t ∈ C) ∧
    (dAsk e = some .acceptAll → C ⊆ L) ∧
    (dAsk e = some (.acceptBatch true) → g ⊆ L)
  post _ e v := ∀ op args r, dAns e v = some (.write op args r) →
    s = some r ∨ ∃ t, W.built ρ op args = some t ∧ ρ r = some t
  ask g e := (dAsk e).elim g (batchGhost W ρ g)
  next g e v := (dAns e v).elim g (batchGhost W ρ g)

/-- **The kept batch of `batchAccept`**: `nil` and the one-element lists of words. -/
def keptL : Set (SExp2 (BitVec 64)) := {t | t = .nil ∨ ∃ w, t = .cons (.atom w) .nil}

end Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch
