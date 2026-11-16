module

public import Silmaril.Wasm.Component.DWiring.Defs
public import Silmaril.Games.Abstract.SessionExt.Defs

/-!
# The component environment extension on sessions: definitions

`DStrategy.ext e D N` (`Silmaril.Wasm.Component.DWiring`) extends an environment `D` of `e`
functions by a node `N` running over it, side by side with copycat on `D`'s functions, through
`splitH e`. Everything lives on the universal interface `sigU`, whose answers are
`Option Payload` (`none` for a trap). Session strategies (`StratSession.threadS`) live on
`sig1 A B`, whose answers are `B ⊕ PUnit` (`.inr ()` for a trap). This module relates the two:

* `sigS = sig1 (Nat × Payload) Payload`: the session view of `sigU`, with the same questions.
* `toOpt`/`ofOpt`: the answer bijection `Payload ⊕ PUnit ≃ Option Payload`.
* `toU : Handler sigS sigU` and `ofU : Handler sigU sigS`: the answer-relabelling handlers
  (`ansH`) along `toOpt` and `ofOpt`. Composing with `ofHandler toU` above relabels the answers
  of a session strategy to `sigU` (`DStrategy.comp_ansH`); `ofHandler ofU` below relabels the
  answers of its imports.
* `splitR e`: the routing of `splitH e` on questions: index below `e` to copycat, else to the
  node, shifted. `routeH (splitR e)` is `splitH e` on session interfaces
  (`SessionExt.extS (splitR e)` is `DStrategy.ext e` on `sigS`).

Theorems in `Silmaril.Wasm.Component.ExtSession.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games Silmaril.Games.Abstract

/-- The session view of `sigU`: the same questions, answers `Payload ⊕ PUnit`. -/
abbrev sigS : Sig.{0} := sig1 (Nat × Payload) Payload

/-- A session answer as a Wasm answer: a trap is `none`. -/
def toOpt : Payload ⊕ PUnit.{1} → Option Payload
  | .inl b => some b
  | .inr _ => none

/-- A Wasm answer as a session answer: `none` is a trap. -/
def ofOpt : Option Payload → Payload ⊕ PUnit.{1}
  | some b => .inl b
  | none => .inr PUnit.unit

/-- Relabel session answers to Wasm answers. -/
def toU : Handler sigS sigU :=
  ansH (F := sigS) (B' := fun _ => Option Payload) fun _ => toOpt

/-- Relabel Wasm answers to session answers. -/
def ofU : Handler sigU sigS :=
  ansH (F := sigU) (B' := fun _ => Payload ⊕ PUnit.{1}) fun _ => ofOpt

/-- The routing of `splitH e`: an index below `e` to copycat, any other to the node, shifted. -/
def splitR (e : Nat) (q : Nat × Payload) : (Nat × Payload) ⊕ (Nat × Payload) :=
  if q.1 < e then .inl q else .inr (q.1 - e, q.2)

end Silmaril.Wasm.Component
