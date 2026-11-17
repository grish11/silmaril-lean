module

public import Silmaril.Wasm.Abstract.NodeLegal.Defs
public import Silmaril.Wasm.Abstract.InstSessionD.Defs
public import Silmaril.Games.DivCompAns.Defs

/-!
# Host-answer domains through the component coercions: definitions

`NodeLegal` states a host-answer domain `Q : Store Nat → Result → Prop` on the plays of an
instance session: an import answer is legal relative to the store at the importer point, the
store of the hidden state `.waiting a s' t e` in which the instance waits for it
(`NodeLegal.RoundLegal`). In the component semantics (`InstSession.semOfSD m`, the node strategy
of `core3SemD`), every import answer the instance receives is given by the coercion `importH m`,
which answers with `payloadAnswer`: values or a trap, **never an exception**. This module states
the two facts that make the domain transparent at the component level.

* `AnsLegal I Q e w`: the import answer `w` to the call `e` is allowed by `Q` **at every store**
  (a store-independent answer legality; an answer legal at every store is legal at the importer
  point, whatever that store is).
* `NonExnLegal Q`: `Q` allows every result that is not an exception, at every store
  (`Cfg.CfgInst.LegalRes` is such a domain: it only constrains `throw a`).
* `NodeWit P m s₀ p u v a b`: a **hidden interaction of the `core3SemD`-style node** `semOfSD m`
  of the instance session from `s₀` producing the visible play `p`: the play `u` of `importH m`,
  the hidden middle play `v`, the read-back instance play `a` and the play `b` of `exportH m`,
  with `Zip u v p` and `Zip a b v`.
* `WitLegal P Q m s₀ a`: the **legality at every importer point** of the witness's hidden
  instance play `a`: `NodeLegal.LegalPlayD` (every import answer allowed by `Q` at the store of
  every hidden `.waiting` state for it, the end of the play included).

Theorems in `Silmaril.Wasm.Abstract.NodeLegalComp.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.NodeLegalComp

open Silmaril.Games
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.InstSession (ssig instSession spullD srelabel)
open Silmaril.Wasm.Component (CoreIface)
open Silmaril.Wasm.Component.Reference (NumInstance importH exportH)
open Silmaril.Wasm.Numerics (Profile)

/-- **An import answer allowed by `Q` at every store.** -/
def AnsLegal (I : ScalarInstance) (Q : Store Nat → Result → Prop) :
    (e : I.E.Op) → I.E.Ar e → Prop :=
  fun e w => ∀ s, Q s (Answer.toResult (ft := I.imports.get e.1) w)

/-- **`Q` allows every result that is not an exception**, at every store. -/
def NonExnLegal (Q : Store Nat → Result → Prop) : Prop :=
  ∀ s r, (∀ a, r ≠ .throw a) → Q s r

/-- **A hidden interaction of the node of `m`** over the instance session from `s₀`, producing
`p`: `importH m` plays `u`, the hidden play is `v`, the read-back instance session plays `a`
and `exportH m` plays `b`. -/
def NodeWit (P : Profile) (m : NumInstance) (s₀ : Store Nat)
    (p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports)))
    (u : List (Move (CoreIface.sig m.imports) (ifaceSig m.inst.imports)))
    (v : List (Move (ifaceSig m.inst.imports) (CoreIface.sig m.exports)))
    (a : List (Move m.inst.E (ifaceSig m.inst.exports)))
    (b : List (Move (ifaceSig m.inst.exports) (CoreIface.sig m.exports))) : Prop :=
  u ∈ Strategy.ofHandler (importH m) ∧ Zip u v p ∧ Zip a b v ∧
    a ∈ (spullD (instSession m.inst P s₀)).toStrategy ∧ b ∈ Strategy.ofHandler (exportH m)

/-- **The hidden instance play is legal at every importer point**, its end included. -/
def WitLegal (P : Profile) (Q : Store Nat → Result → Prop) (m : NumInstance) (s₀ : Store Nat)
    (a : List (Move m.inst.E (ifaceSig m.inst.exports))) : Prop :=
  NodeLegal.LegalPlayD m.inst P Q s₀ (a.map srelabel)

end Silmaril.Wasm.Abstract.NodeLegalComp
