module

public import Silmaril.Wasm.Component.Reference.Adequacy.Defs
import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Adequate
import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Witness

/-!
# Adequacy of the component IR against the reference machine: theorems

For simple components (`Simple`) in the fragment `Simple.Adequate` (float-free, within the flat
arities, the module instantiated as the IR assumes, no imports), at every silmaril profile `P`
and every component choice profile `prof` (no determinism is assumed):

* **completeness, specification to reference** (`Simple.specToRef`, `Simple.seq_specToRef`):
  every terminating outcome of the canonical-ABI specification `exportSpec` is a reference
  behaviour, the converse of `refToSpec`; for sequences of calls on one instance, every chain of
  returned calls threading the Core store (`SeqSpec`) with a terminating outcome of a last call
  (`specAt`) is a behaviour of `seqBehaviours`;
* **completeness, IR to reference** (`Simple.complete`, `Simple.complete_seq`): every play of
  `c.toComp.den (modSem P)` of a call (resp. of resolved calls and a last call) with a
  terminating answer, as `IRObs` (resp. `SeqIRObs`) prescribes, is a reference behaviour of the
  same calls; with `Simple.sound` and `Simple.sound_seq` (`Sound.Thms`) the terminating reference
  behaviours are exactly these plays;
* **the plays of the IR** (`Simple.den_shape`): every play of the IR denotation of a simple
  component is complete export rounds, possibly followed by one pending export question
  (`exportRounds`); the trap-last ones (`Simple.trapLast_shape`) are typed returned calls
  (`seqMoves`), possibly followed by a pending question or by a trap answer to it;
* **finite adequacy** (`Simple.adequacy`): `RefPubEquiv P prof c c'` holds exactly when `c` and
  `c'` have the same export types and the same trap-last plays (`trapLastPlays`).

`Simple.adequacy` is not equality of IR strategies: a core instance's strategy keeps its store
after a trap and answers later questions, which the reference machine (REF: a trap locks the
store down) cannot observe. The witnesses `pokePeekS` and `zeroS` (`Adequacy.Defs`) show it, at
every deterministic profile and component choice profile: they are adequate
(`pokePeekS_adequate`, `zeroS_adequate`) and `RefPubEquiv` (`witness_equiv`), and their IR
strategies differ (`witness_ne`, `witness_play`: `poke · trap · peek · 1`). The equality
restricted to trap-last plays is the strongest statement `RefPubEquiv` can give
(`refPubEquiv_not_den_eq`).

Not claimed: divergence and infinite plays (finite plays cannot tell a diverging call from a call
that never answers; `RefPubEquiv` compares terminating outcomes only; the infinite case needs the
game-level infinite closure, `DStrategy` `div`/`inf`), contextual full abstraction, and the
correctness of the parser from bytes to `Comp`.

Proofs: `Silmaril.Proofs.Wasm.Component.Reference.Adequacy.{Games,IRPlays,LiftTrap,CallAt,RefRun,
RefSeq,Transfer,Main,Adequate,WitnessInst,WitnessRun,Witness}`.
-/

public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Games Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

/-- **Specification outcomes of one call are reference behaviours** (proved): the converse of
`refToSpec` for terminating outcomes. -/
theorem Simple.specToRef (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (j : Fin c.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) {b : Outcome}
    (hb : b ∈ exportSpec P c c.exports[j] vs) (hterm : b.Term) :
    b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name (vs.map toRefVal) :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.specToRef P prof c hc.good hc.floatFree
    hc.inst hc.arity j vs hvs hb hterm

/-- **Specification sequences are reference behaviours** (proved): the converse of
`seq_refToSpec` for terminating last outcomes. -/
theorem Simple.seq_specToRef (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : c.mod.IsInst I)
    (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal))
    (s : Silmaril.Wasm.Execution.Core.Store Nat) (j : Fin c.exports.length) (vs : List IVal)
    (ht : TypedCalls c calls) (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (hseq : SeqSpec P c I I.store (specCalls c calls) wss s) {b : Outcome}
    (hb : b ∈ specAt P c I c.exports[j] vs s) (hterm : b.Term) :
    (wss.map (·.map toRefVal), b) ∈ seqBehaviours prof (refHost P) () c.toRef
      (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal) :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.seq_specToRef P prof c hc.good hc.floatFree
    hc.inst hc.arity hI calls wss s j vs ht hvs hseq hb hterm

/-- **Completeness of the IR for one call** (proved): a play of the IR denotation of a call with
a terminating answer is a reference behaviour of the call. -/
theorem Simple.complete (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (j : Fin c.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome) (hterm : b.Term)
    (hb : IRObs (k := c.toComp.exports.length) (c.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs b) :
    b ∈ exportBehaviours prof (refHost P) () c.toRef [] c.exports[j].name (vs.map toRefVal) :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.complete P prof c hc j vs hvs b hterm hb

/-- **Completeness of the IR for sequences of calls** (proved): a play of the IR denotation of
resolved calls `calls` with results `wss` and a last call with a terminating answer, as
`SeqIRObs` prescribes, is a reference behaviour of the same calls; the calls are typed. -/
theorem Simple.complete_seq (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal))
    (hlen : calls.length = wss.length) (j : Fin c.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : Outcome) (hterm : b.Term)
    (hb : SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs b) :
    TypedCalls c calls ∧ (wss.map (·.map toRefVal), b) ∈ seqBehaviours prof (refHost P) ()
      c.toRef (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal) :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.complete_seq P prof c hc calls wss hlen j vs
    hvs b hterm hb

/-- **The plays of a simple component's IR** (proved, every core semantics): complete export
rounds, possibly followed by one pending export question. -/
theorem Simple.den_shape (C : CoreSem NumModule) (c : Simple)
    {p : List (Move (sigN 0) (sigN c.toComp.exports.length))} (hp : p ∈ c.toComp.den C) :
    (∃ L, p = exportRounds L) ∨ ∃ L q, p = exportRounds L ++ [.inr (.ask q)] :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.den_shape' C c hp

/-- **The trap-last plays of a simple component's IR** (proved): typed returned calls, possibly
followed by a pending export question or by a trap answer to it. -/
theorem Simple.trapLast_shape (P : Profile) {c : Simple} (hc : c.Adequate)
    {p : List (Move (sigN 0) (sigN c.toComp.exports.length))}
    (hp : p ∈ c.toComp.den (modSem P)) (htl : TrapLast (p.map forgetMove)) :
    ∃ (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal)),
      TypedCalls c calls ∧ calls.length = wss.length ∧
      (p = seqMoves c calls wss ∨ ∃ q, p = seqMoves c calls wss ++ [.inr (.ask q)] ∨
        p = seqMoves c calls wss ++ [.inr (.ask q), .inr (.ans q none)]) :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.trapLast_shape hc hp htl

/-- **Finite adequacy of the component IR** (proved, every profile and component choice
profile): for adequate simple components, the public component interaction equivalence on the
reference machine holds exactly when the export types and the trap-last IR plays are the same.
Terminating outcomes only; not contextual full abstraction. -/
theorem Simple.adequacy (P : Profile) (prof : ProfileKind) {c c' : Simple} (hc : c.Adequate)
    (hc' : c'.Adequate) :
    RefPubEquiv P prof c c' ↔ SameTypes c c' ∧
      trapLastPlays (c.toComp.den (modSem P)) = trapLastPlays (c'.toComp.den (modSem P)) :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.adequacy P prof hc hc'

/-! ## The trap witnesses -/

/-- `pokePeekS` is in the fragment (proved; its instance is computed by kernel evaluation). -/
theorem pokePeekS_adequate : pokePeekS.Adequate :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.pokePeekS_adequate

/-- `zeroS` is in the fragment (proved). -/
theorem zeroS_adequate : zeroS.Adequate :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.zeroS_adequate

/-- **The witnesses are publicly equivalent on the reference machine** (proved, every
deterministic profile and component choice profile). -/
theorem witness_equiv (o : Silmaril.Wasm.SingleThreaded.GrowOracle) (prof : ProfileKind) :
    RefPubEquiv (Silmaril.Wasm.SingleThreaded.profile o) prof pokePeekS zeroS :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.witness_equiv o prof

/-- **The IR plays `poke · trap · peek · 1` for `pokePeekS` and not for `zeroS`** (proved,
every deterministic profile), read at `sigU`. -/
theorem witness_play (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    ∃ p, p ∈ pubPlays (pokePeekS.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o))) ∧
      p ∉ pubPlays (zeroS.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o))) :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.witness_play o

/-- **The IR strategies of the witnesses differ** (proved, every deterministic profile). -/
theorem witness_ne (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    pokePeekS.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o)) ≠
      zeroS.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o)) :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.witness_ne o

/-- **`RefPubEquiv` does not determine the IR plays** (proved): at every deterministic profile
and component choice profile, there are adequate simple components that are publicly
equivalent on the reference machine with different plays. -/
theorem refPubEquiv_not_den_eq (o : Silmaril.Wasm.SingleThreaded.GrowOracle)
    (prof : ProfileKind) :
    ¬ ∀ c c' : Simple, c.Adequate → c'.Adequate →
      RefPubEquiv (Silmaril.Wasm.SingleThreaded.profile o) prof c c' →
      pubPlays (c.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o))) =
        pubPlays (c'.toComp.den (modSem (Silmaril.Wasm.SingleThreaded.profile o))) :=
  Silmaril.Proofs.Wasm.Component.Reference.Adequacy.refPubEquiv_not_den_eq o prof

end Silmaril.Wasm.Component.Reference
