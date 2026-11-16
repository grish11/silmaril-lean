module

public import Silmaril.Wasm.Component.Reference.Link.Defs
public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Defs

/-!
# The IR side of linked sessions: definitions

**Scope.** `Linked2`: two components linked through the canonical ABI, the import-free
exporter `exp` answering the imports of the importer `imp` (`Link.Defs`). This module is about
`Linked2` only. The general linked composition (arbitrary component graphs, and a linked
adequacy theorem for them) waits on the composition closure of `DStrategy` (the H2 owner's
part, asked on #207). The parser from bytes to these components and F6 are pending.

`Linked2.ExpRun` (`Link.Defs`) answers the importer's component import calls by the exporter's
specification with its Core store threaded, but its `trap` constructor ends the run: an
exporter trap can only answer the **last** import call. In the resumable sessions of
`SessionAdequacy` (and `instSession`/`threadS` in `Silmaril.Wasm.Abstract.InstSession` and
`StratSession`), a trap aborts the current call, not the instance: the exporter's instance
continues from the store the trap left. This module defines that reading on the IR side.

* `Linked2.ExpRunT P l I s ds s'`: the import calls `ds`, in order, answered by the exporter's
  specification at its instance `I` from the Core store `s` to `s'`; a call is a returned call
  (`RetAt`) or a trapped call (`TrapAt`, answered `none`), and **both** thread the store, so a
  trapped exporter call may be followed by further import calls. A new relation beside
  `ExpRun`, whose proofs are unchanged.
* `Linked2.SessRound l Ii`: one export call of the linked component, on the importer's side: the
  export `j` called on `vs`, the importer's core question `f`, its core import calls `cs` (with
  their answers), its core answer `w`, and the component import calls `dss` they correspond to
  (`ImpRel`). `SessRound.Ok`: the round is well formed (the lowering, the core export, the
  arguments and `ImpRel`). `instMoves` is its play of the importer's core instance and
  `linkMoves` its two-move play of the linked component (the import calls hidden).
* `Linked2.SessToIR`: rounds whose instance plays are, one after another, a play of the
  importer's instance from its store, and whose component import calls, all together and in
  order, are an `ExpRunT` from the exporter instance's store, are the linked plays of
  `l.toComp.den (impSem P)`, one after another (proved: `Linked2.sessToIR`, `Thms`).

An import call answered `none` (an exporter trap) is passed to the importer's core instance as
a trap (`ImpRel`: `payloadAnswer _ none = .trap`); the core call then traps and the importer's
round answers `none` (`Thms`: `trapImport_path`, `impRel_trap`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component

namespace Linked2

section IR

open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

/-- **Import calls answered by the exporter's specification, traps continuing**: each call of
import `k` on `ws` is a returned call (`RetAt`) or a trapped call (`TrapAt`, answered `none`) of
the wired export `wire[k]` from the current store; both move the exporter's Core store on, and
the run ends at `s'`. -/
inductive ExpRunT (P : Profile) (l : Linked2) (I : ScalarInstance) :
    Store Nat → List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload) → Store Nat → Prop
  | nil (s : Store Nat) : ExpRunT P l I s [] s
  | ret {s s₁ s' : Store Nat} {k : Fin l.imp.imports.length}
      {ws us : List Silmaril.Wasm.Component.Val}
      {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
      (w : Fin l.exp.exports.length) :
      l.wire[k.val]? = some w.val → RetAt P l.exp I l.exp.exports[w] ws s us s₁ →
      ExpRunT P l I s₁ ds s' → ExpRunT P l I s (⟨(k, .vals ws), some (.vals us)⟩ :: ds) s'
  | trap {s s₁ s' : Store Nat} {k : Fin l.imp.imports.length}
      {ws : List Silmaril.Wasm.Component.Val}
      {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)}
      (w : Fin l.exp.exports.length) :
      l.wire[k.val]? = some w.val → TrapAt P l.exp I l.exp.exports[w] ws s s₁ →
      ExpRunT P l I s₁ ds s' → ExpRunT P l I s (⟨(k, .vals ws), none⟩ :: ds) s'

/-- **One export call of a linked session, on the importer's side.** -/
structure SessRound (l : Linked2) (Ii : ScalarInstance) where
  /-- The export of the importer (and of the linked component). -/
  j : Fin l.imp.exports.length
  /-- The IR arguments. -/
  vs : List Silmaril.Wasm.Component.Val
  /-- The core question of the importer's instance. -/
  f : Ii.F.Op
  /-- The core import calls, with their answers. -/
  cs : List (Σ e : Ii.E.Op, Ii.E.Ar e)
  /-- The core answer. -/
  w : Ii.F.Ar f
  /-- The component import calls of each core import call. -/
  dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))

namespace SessRound

variable {l : Linked2} {Ii : ScalarInstance} (d : SessRound l Ii)

/-- The round is well formed: the arguments lower to the core question of the lifted core
export, and the core import calls correspond to the component import calls (`ImpRel`). -/
def Ok : Prop :=
  ∃ xs : List Flat, checkLower l.imp.exports[d.j].ty.params d.vs = some xs ∧
    d.f.1.val = l.imp.exports[d.j].core ∧ d.f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat ∧
    List.Forall₂ (ImpRel l.imp Ii) d.cs d.dss

/-- The play of the importer's core instance. -/
def instMoves : List (Silmaril.Games.Move Ii.E Ii.F) :=
  .inr (.ask d.f) :: callMoves d.cs ++ [.inr (.ans d.f d.w)]

/-- The lifted answer of the round. -/
def ans : Option Payload :=
  (answerPayload d.w).bind (Adapter.up (.lift l.imp.exports[d.j].ty))

/-- The play of the linked component: the export question and the lifted answer. -/
def linkMoves :
    List (Silmaril.Games.Move l.toComp.imports.sig (sigN l.toComp.exports.length)) :=
  [.inr (.ask (⟨d.j, by simp [exports_length_toComp]⟩, .vals d.vs)),
    .inr (.ans (m := (⟨d.j, by simp [exports_length_toComp]⟩, .vals d.vs)) d.ans)]

end SessRound

/-- **The IR side of linked sessions, exporter traps continuing**: for rounds `L` whose
instance plays, one after another, are a play of the importer's instance from its store, and
whose component import calls, all together and in order, are answered by the exporter's
specification from its instance's store with traps continuing (`ExpRunT`), the linked plays,
one after another, are a play of `l.toComp.den (impSem P)`. -/
def SessToIR : Prop :=
  ∀ (P : Profile) (l : Linked2), l.exp.Good → l.imp.Good →
    ∀ (Ie : ScalarInstance), l.exp.mod.IsInst Ie → ∀ (Ii : ScalarInstance), l.imp.mod.IsInst Ii →
    ∀ (L : List (SessRound l Ii)), (∀ d ∈ L, d.Ok) →
    ∀ (q : Ii.HState), Ii.Path P (.idle Ii.store) (L.flatMap SessRound.instMoves) q →
    ∀ (s' : Store Nat), ExpRunT P l Ie Ie.store (L.flatMap fun d => d.dss.flatten) s' →
    L.flatMap SessRound.linkMoves ∈ l.toComp.den (impSem P)

end IR

end Linked2

end Silmaril.Wasm.Component.Reference
