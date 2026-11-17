module

public import Silmaril.Wasm.Cfg.CfgLegal.Defs
public import Silmaril.Wasm.Cfg.CfgInst.Thms
public import Silmaril.Wasm.Abstract.NodeLegal.Thms
public import Silmaril.Wasm.Component.DWiringMono.Thms

/-!
# The legal typed host-answer domain of instance sessions: theorems

Deterministic profile `profile o` throughout. `instSession I (profile o) s₀` is the Core 3.0
instance session (the node session of `core3SemD`), `threadS (instTripleL I (profile o)) s₀` the
legal one (the node session of `legalSemD`), `threadS (cfgInstTripleL I) s₀` the CFG-built one.

**(a) The domain.** `instTripleL_eq`: `instTripleL` is `NodeLegal.instTripleQ` at the domain
`LegalRes` (by definition), so the results of `Abstract.NodeLegal` apply. `roundLegal_iff` reads
the round legality: each import answer of the log throws only below `s'.exns.length`, `s'` the
store of every hidden state `.waiting` of the instance waiting for it.

**(b) The legal session is the exact legal pullback of the Core 3.0 instance session**, on every
observation of the session strategy (`StratSession.threadS`; finite plays, plays ending in a call,
`div`, `inf`):

* `legalSession_le`: the legal session refines the instance session;
* `mem_legalSession`: `q` is a play of the legal session iff it is a play of `instSession` and
  `LegalPlay`;
* `pending_legalSession`: a play ending in an import call: iff a play of `instSession` legal up to
  the call (`LegalPlayD` of the play before the call);
* `div_legalSession`: iff a divergence of `instSession` that is `LegalPlayD`;
* `inf_legalSession`: iff an infinite play of `instSession` all of whose prefixes are `LegalPlay`.

**(c) The CFG-built session is that pullback**, from a store of the domain (`CfgInst.InstDom`):
`mem_cfgSession`, `pending_cfgSession`, `div_cfgSession`, `inf_cfgSession`
(by `CfgInst.threadS_instTripleL_eq`).

**(d) Nodes of the component semantics.** The node strategy of `legalSemD` at `m` is
`semOfSD m (threadS (instTripleL m.inst _) m.inst.store)`:

* `legalSemD_le`, `denUD_legalSemD_le`: `legalSemD` refines `core3SemD` node by node, hence every
  component's denotation under `legalSemD` refines the one under `core3SemD` (`denUD_mono`);
* `mem_legalSemD_sem`, `div_legalSemD_sem`: a play (a divergence) of the `legalSemD` node is the
  visible part of an interaction through `importH m`, the read-back `core3SemD` instance session
  and `exportH m`, whose hidden instance play is `LegalPlay` (`LegalPlayD`);
* `cfgSemD_sem_eq`, `mem_cfgSemD_sem`, `div_cfgSemD_sem`: on an instance of the domain the
  CFG-built node is the `legalSemD` node, with the same characterizations;
* `denUD_cfgSemD_eq`, `denUD_cfgSemD_le`: on a component all of whose core instances are in the
  domain, its CFG-built denotation is its `legalSemD` denotation, which refines its `core3SemD`
  denotation.

**(e) Injectivity of the legal object.** `legalSession_eq_iff`: two legal sessions of `I` (at
deterministic profiles `profile o`, `profile o'`) are equal iff their start stores are
observationally equivalent (`StratThread.ObsEq`, a bisimulation of round stores) for the legal
parts `restrictLog (RoundLegal …) (instTripleS …)`. So the legal session determines, and is
determined by, the legal restriction of the instance triple up to bisimilarity of stores;
`cfgSession_eq_iff` is the same for the CFG-built sessions, from stores of the domain. This is
the legal counterpart of `InstSession.instSession_eq_iff`. The two equivalences are not compared
here: legality reads the hidden call stores, so equal Core 3.0 sessions are not shown to have
equal legal sessions, nor conversely.

## What is not claimed

* **No raw `core3SemD` equality for instances with imports.** `core3SemD` also has the plays in
  which an import throws a dangling exception (`throw a` with `a ≥ s.exns.length` at the call
  store); these are exactly the plays that are not `LegalPlay`, and no CFG reading of them is
  claimed (see `CfgInst.Thms`, "What is not claimed"). `legalSemD` (and `cfgSemD`) equal
  `core3SemD` only where nothing is restricted: instances without imports
  (`CfgInst.core3SemD_sem_eq_cfgInstSessionsL`).
* **The compositional pullback is not proved.** For components, only refinement
  (`denUD_legalSemD_le`) is proved. That `c.denUD (legalSemD _)` is exactly the part of
  `c.denUD (core3SemD _)` whose hidden node plays are legal needs a characterization of the
  interactions of `Comp.denUD` (node composition, `implsN`, the wiring) with legality reflected
  through each hidden interface; at the node level the hidden instance play is already the place
  where legality is stated (`mem_legalSemD_sem`). Infinite plays at the node level (through
  `DStrategy.InfInteraction`) are covered only by the refinement.
* **No reference-equivalence injection for the legal object.** The concrete injections
  (`Linked2`/`LinkedG` `compSession_inj_full`, `refSessEquivFull_iff_denD`) relate the reference
  machine's `RefSessEquivFull` to the unrestricted component session objects. Their legal
  counterparts are left to the owner of those modules: a reference equivalence restricted to
  legal environments, and a statement of which import answers of internally linked components are
  legal at the importer's call store. Without those, `legalSession_eq_iff` is the injection proved
  here.
-/

public section

namespace Silmaril.Wasm.Cfg.CfgLegal

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Games.Abstract.StratObs (callMoves)
open Silmaril.Wasm.Abstract.InstSession (ssig instSession core3SemD semOfSD spullD srelabel
  threadSemSD)
open Silmaril.Wasm.Cfg.CfgInst (LegalRes instTripleL cfgInstTripleL legalSemD cfgInstSessionsL
  InstDom)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Component (Comp CoreIface denUD_mono)
open Silmaril.Wasm.Component.Reference (NumInstance importH exportH)
open Silmaril.Wasm.Cfg.SessionCheck (CompIn)

variable {I : ScalarInstance}

/-! ## (a) The domain -/

/-- `instTripleL` is the instance triple restricted on its Core events by `LegalRes`. -/
theorem instTripleL_eq (P : Numerics.Profile) :
    instTripleL I P = Abstract.NodeLegal.instTripleQ I P LegalRes := rfl

/-- **The round legality of `LegalRes`**: every import answer throws only exceptions of the store
of every hidden state waiting for it. -/
theorem roundLegal_iff {P : Numerics.Profile} {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)} :
    Abstract.NodeLegal.RoundLegal I P LegalRes s a c ↔ ∀ c₁ x c₂, c = c₁ ++ x :: c₂ → ∀ s' t,
      I.Path P (.idle s) (.inr (.ask a) :: (callMoves c₁ ++ [.inl (.ask x.1)])) (.waiting a s' t x.1) →
        x.2.ThrowsBelow s'.exns.length := by
  simp only [Abstract.NodeLegal.RoundLegal, CfgInst.legalRes_toResult_iff]

variable {o : GrowOracle} {s₀ : Store Nat}

/-! ## (b) The legal session is the legal pullback of the instance session -/

/-- **The legal session refines the instance session.** -/
theorem legalSession_le (s₀ : Store Nat) :
    threadS (instTripleL I (profile o)) s₀ ≤ instSession I (profile o) s₀ :=
  Abstract.NodeLegal.threadS_instTripleQ_le s₀

/-- **Finite plays**: the legal plays of the instance session. -/
theorem mem_legalSession {q : List (Move I.E (ssig I.exports))} :
    q ∈ (threadS (instTripleL I (profile o)) s₀).toStrategy ↔
      q ∈ (instSession I (profile o) s₀).toStrategy ∧ LegalPlay I (profile o) s₀ q :=
  Abstract.NodeLegal.mem_threadS_instTripleQ

/-- **Pending calls**: the plays of the instance session ending in a call, legal up to it. -/
theorem pending_legalSession {q : List (Move I.E (ssig I.exports))} {e : I.E.Op} :
    q ++ [.inl (.ask e)] ∈ (threadS (instTripleL I (profile o)) s₀).toStrategy ↔
      q ++ [.inl (.ask e)] ∈ (instSession I (profile o) s₀).toStrategy ∧
        LegalPlayD I (profile o) s₀ q :=
  Abstract.NodeLegal.pending_threadS_instTripleQ

/-- **Divergences**: the divergences of the instance session legal up to their end. -/
theorem div_legalSession {q : List (Move I.E (ssig I.exports))} :
    q ∈ (threadS (instTripleL I (profile o)) s₀).div ↔
      q ∈ (instSession I (profile o) s₀).div ∧ LegalPlayD I (profile o) s₀ q :=
  Abstract.NodeLegal.div_threadS_instTripleQ

/-- **Infinite plays**: the infinite plays of the instance session with legal prefixes. -/
theorem inf_legalSession {J : Set (List (Move I.E (ssig I.exports)))} :
    J ∈ (threadS (instTripleL I (profile o)) s₀).inf ↔
      J ∈ (instSession I (profile o) s₀).inf ∧ ∀ q ∈ J, LegalPlay I (profile o) s₀ q :=
  Abstract.NodeLegal.inf_threadS_instTripleQ

/-! ## (c) The CFG-built session, from a store of the domain -/

/-- **Finite plays of the CFG-built session**: the legal plays of the instance session. -/
theorem mem_cfgSession (hd : InstDom I s₀) {q : List (Move I.E (ssig I.exports))} :
    q ∈ (threadS (cfgInstTripleL I) s₀).toStrategy ↔
      q ∈ (instSession I (profile o) s₀).toStrategy ∧ LegalPlay I (profile o) s₀ q := by
  rw [← CfgInst.threadS_instTripleL_eq (o := o) hd]; exact mem_legalSession

/-- **Pending calls of the CFG-built session.** -/
theorem pending_cfgSession (hd : InstDom I s₀) {q : List (Move I.E (ssig I.exports))}
    {e : I.E.Op} :
    q ++ [.inl (.ask e)] ∈ (threadS (cfgInstTripleL I) s₀).toStrategy ↔
      q ++ [.inl (.ask e)] ∈ (instSession I (profile o) s₀).toStrategy ∧
        LegalPlayD I (profile o) s₀ q := by
  rw [← CfgInst.threadS_instTripleL_eq (o := o) hd]; exact pending_legalSession

/-- **Divergences of the CFG-built session.** -/
theorem div_cfgSession (hd : InstDom I s₀) {q : List (Move I.E (ssig I.exports))} :
    q ∈ (threadS (cfgInstTripleL I) s₀).div ↔
      q ∈ (instSession I (profile o) s₀).div ∧ LegalPlayD I (profile o) s₀ q := by
  rw [← CfgInst.threadS_instTripleL_eq (o := o) hd]; exact div_legalSession

/-- **Infinite plays of the CFG-built session.** -/
theorem inf_cfgSession (hd : InstDom I s₀) {J : Set (List (Move I.E (ssig I.exports)))} :
    J ∈ (threadS (cfgInstTripleL I) s₀).inf ↔
      J ∈ (instSession I (profile o) s₀).inf ∧ ∀ q ∈ J, LegalPlay I (profile o) s₀ q := by
  rw [← CfgInst.threadS_instTripleL_eq (o := o) hd]; exact inf_legalSession

/-! ## (d) Nodes of the component semantics -/

/-- **`legalSemD` refines `core3SemD`, node by node.** -/
theorem legalSemD_le : (legalSemD (profile o)).Le (core3SemD (profile o)) :=
  fun m => Abstract.NodeLegal.semOfSD_instTripleQ_le m m.inst.store

/-- **Every component's denotation under `legalSemD` refines its `core3SemD` denotation.** -/
theorem denUD_legalSemD_le (c : Comp NumInstance) :
    c.denUD (legalSemD (profile o)) ≤ c.denUD (core3SemD (profile o)) :=
  denUD_mono legalSemD_le c

/-- **Finite plays of a `legalSemD` node**: interactions through the coercions whose hidden
instance play is a legal play of the `core3SemD` instance session. -/
theorem mem_legalSemD_sem {m : NumInstance}
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ ((legalSemD (profile o)).sem m).toStrategy ↔
      ∃ u ∈ Strategy.ofHandler (importH m), ∃ v, Zip u v p ∧ ∃ a b, Zip a b v ∧
        a ∈ (spullD (instSession m.inst (profile o) m.inst.store)).toStrategy ∧
        LegalPlay m.inst (profile o) m.inst.store (a.map srelabel) ∧
        b ∈ Strategy.ofHandler (exportH m) :=
  Abstract.NodeLegal.mem_semOfSD_instTripleQ

/-- **Divergences of a `legalSemD` node**: interactions through the coercions whose hidden
instance play is a legal divergence of the `core3SemD` instance session. -/
theorem div_legalSemD_sem {m : NumInstance}
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ ((legalSemD (profile o)).sem m).div ↔
      ∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (importH m) ∧ ∃ a b, Zip a b v ∧
        a ∈ (spullD (instSession m.inst (profile o) m.inst.store)).div ∧
        LegalPlayD m.inst (profile o) m.inst.store (a.map srelabel) ∧
        b ∈ Strategy.ofHandler (exportH m) :=
  Abstract.NodeLegal.div_semOfSD_instTripleQ

/-- **On an instance of the domain the CFG-built node is the `legalSemD` node.** -/
theorem cfgSemD_sem_eq {m : NumInstance} (hm : InstDom m.inst m.inst.store) :
    cfgSemD.sem m = (legalSemD (profile o)).sem m :=
  (CfgInst.legalSemD_sem_eq hm).symm

/-- **Finite plays of a CFG-built node** of the domain: interactions whose hidden instance play is
a legal play of the `core3SemD` instance session. -/
theorem mem_cfgSemD_sem {m : NumInstance} (hm : InstDom m.inst m.inst.store)
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ (cfgSemD.sem m).toStrategy ↔
      ∃ u ∈ Strategy.ofHandler (importH m), ∃ v, Zip u v p ∧ ∃ a b, Zip a b v ∧
        a ∈ (spullD (instSession m.inst (profile o) m.inst.store)).toStrategy ∧
        LegalPlay m.inst (profile o) m.inst.store (a.map srelabel) ∧
        b ∈ Strategy.ofHandler (exportH m) := by
  rw [cfgSemD_sem_eq (o := o) hm]; exact mem_legalSemD_sem

/-- **Divergences of a CFG-built node** of the domain. -/
theorem div_cfgSemD_sem {m : NumInstance} (hm : InstDom m.inst m.inst.store)
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ (cfgSemD.sem m).div ↔
      ∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (importH m) ∧ ∃ a b, Zip a b v ∧
        a ∈ (spullD (instSession m.inst (profile o) m.inst.store)).div ∧
        LegalPlayD m.inst (profile o) m.inst.store (a.map srelabel) ∧
        b ∈ Strategy.ofHandler (exportH m) := by
  rw [cfgSemD_sem_eq (o := o) hm]; exact div_legalSemD_sem

/-- **The CFG-built denotation is the `legalSemD` denotation** on components whose core instances
are in the domain. -/
theorem denUD_cfgSemD_eq (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => InstDom m.inst m.inst.store) c) :
    c.denUD cfgSemD = c.denUD (legalSemD (profile o)) :=
  (CfgInst.denUD_legalSemD_eq_cfgInstSessionsL c hc).symm

/-- **The CFG-built denotation refines the Core 3.0 denotation** on components whose core
instances are in the domain. -/
theorem denUD_cfgSemD_le (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => InstDom m.inst m.inst.store) c) :
    c.denUD cfgSemD ≤ c.denUD (core3SemD (profile o)) := by
  rw [denUD_cfgSemD_eq (o := o) c hc]; exact denUD_legalSemD_le c

/-! ## (e) Injectivity of the legal object -/

/-- **Legal sessions identify exactly the bisimilar stores of the legal parts.** -/
theorem legalSession_eq_iff {o' : GrowOracle} {s s' : Store Nat} :
    threadS (instTripleL I (profile o)) s = threadS (instTripleL I (profile o')) s' ↔
      StratThread.ObsEq
        (SessionLegal.restrictLog (Abstract.NodeLegal.RoundLegal I (profile o) LegalRes)
          (Abstract.InstSession.instTripleS I (profile o)))
        (SessionLegal.restrictLog (Abstract.NodeLegal.RoundLegal I (profile o') LegalRes)
          (Abstract.InstSession.instTripleS I (profile o'))) s s' := by
  rw [instTripleL_eq, instTripleL_eq, Abstract.NodeLegal.threadS_instTripleQ_eq,
    Abstract.NodeLegal.threadS_instTripleQ_eq]
  exact SessionLegal.threadS_restrictLog_eq_iff (Abstract.InstSession.storeDet_instTripleS o)
    (Abstract.InstSession.storeDet_instTripleS o') Abstract.InstSession.noPlainTrap_instTripleS
    Abstract.InstSession.noPlainTrap_instTripleS

/-- **CFG-built sessions from stores of the domain identify exactly the bisimilar stores of the
legal parts.** -/
theorem cfgSession_eq_iff {s s' : Store Nat} (hd : InstDom I s) (hd' : InstDom I s') :
    threadS (cfgInstTripleL I) s = threadS (cfgInstTripleL I) s' ↔
      StratThread.ObsEq
        (SessionLegal.restrictLog (Abstract.NodeLegal.RoundLegal I (profile o) LegalRes)
          (Abstract.InstSession.instTripleS I (profile o)))
        (SessionLegal.restrictLog (Abstract.NodeLegal.RoundLegal I (profile o) LegalRes)
          (Abstract.InstSession.instTripleS I (profile o))) s s' := by
  rw [← CfgInst.threadS_instTripleL_eq (o := o) hd, ← CfgInst.threadS_instTripleL_eq (o := o) hd']
  exact legalSession_eq_iff

end Silmaril.Wasm.Cfg.CfgLegal
