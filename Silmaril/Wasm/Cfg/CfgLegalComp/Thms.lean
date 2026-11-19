module

public import Silmaril.Wasm.Cfg.CfgLegalComp.Defs
public import Silmaril.Wasm.Cfg.CfgLegal.Thms
public import Silmaril.Wasm.Abstract.NodeLegalComp.Thms
import Silmaril.Proofs.Wasm.Cfg.CfgLegalComp

/-!
# Exact legality of component denotations: theorems

Deterministic profile `profile o` for the equalities; the legality of hidden interactions holds at
every profile.

**The boundary** (`NodeLegalComp`). Every import answer an instance receives inside a
`core3SemD`/`legalSemD` node comes from the node's coercion `importH m`, which answers with
`payloadAnswer`, i.e. `.values` or `.trap`, never `.throw`. `CfgInst.LegalRes s r` only
constrains exceptions (`∀ a, r = .throw a → a < s.exns.length`), so it holds for every such
answer at every store, in particular at the importer's `.waiting` store
(`nonExnLegal_legalRes`). It asks nothing of values, arity, references or stores: values are
typed by `Answer`'s type. This is the exact strength of the domain at this boundary.

**Exact component legality.**

* `nodeHidLegal`, `compLegal`: every hidden interaction of every core node of every component is
  legal at every importer point (any profile, any wiring: wiring programs, `ext`, nested
  instances and hidden composition act above `importH m`, on `CoreIface.sig m.imports`).
* `legalSemD_sem_eq`, `legalSemD_eq`: **`legalSemD (profile o) = core3SemD (profile o)`** at the
  node interface (`DCoreSem` equality: finite plays, divergences, infinite plays).
* `denUD_legalSemD_eq`, `denD_legalSemD_eq`: hence the component denotations are equal, for every
  component (no domain restriction).
* `mem_denUD_legalSemD_iff`, `pending_denUD_legalSemD_iff`, `div_denUD_legalSemD_iff`
  (divergence by hidden chatter included), `inf_denUD_legalSemD_iff`: the observations of
  `c.denUD (legalSemD _)` are exactly those of `c.denUD (core3SemD _)` whose hidden node
  interactions are legal at every importer point (`CompLegal`), which they all are.
* `mem_legalSemD_sem_iff`, `div_legalSemD_sem_iff`, `inf_legalSemD_sem_iff`: node-level forms
  with explicit witnesses (`NodeLegalComp.NodeWit`, `WitLegal`); for infinite plays,
  `NodeLegalComp.inf_inner_lift` gives one coherent inner infinite interaction with legal stages.

**The CFG-built component semantics** (`CfgLegal.cfgSemD`), on components all of whose core
instances are in the CFG domain (`CompIn (fun m => InstDom m.inst m.inst.store)`):

* `cfgSemD_sem_eq_core3`, `denUD_cfgSemD_eq_core3`, `denD_cfgSemD_eq_core3`:
  **`c.denUD cfgSemD = c.denUD (core3SemD (profile o))`**, imports included.

## What is not claimed

* **Not about the session interface.** On `ssig` (before `importH`) an environment may answer
  `throw a`, at a dangling address too. The legal session (`threadS (instTripleL …)`) drops the
  plays with dangling throws; equality of the unrestricted instance session `instSession` with a
  CFG reading **is not established**. (No inequality is proved either: a raw Core and a CFG
  reading might both have matching dangling throws.) The node-level equality does not prove
  native/Core equality on arbitrary throwing `ssig` environments; the raw dangling backward bridge
  (`DanglingExn`) is separate.
* **By design of the IR boundary**, the component semantics has no cross-node exception
  propagation: an exception escaping an export becomes `none` (`answerPayload`, a trap), and an
  import answer is never an exception (`payloadAnswer`). The equalities above hold because of
  this boundary; they say nothing about a reference interface that would pass exceptions between
  instances.
* **No reference injection** is derived here: that needs the reference relation to be stated at
  this same boundary (`CfgLegalOwner`).
-/

public section

namespace Silmaril.Wasm.Cfg.CfgLegalComp

open Silmaril.Games
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.InstSession (core3SemD semOfSD spullD instSession)
open Silmaril.Wasm.Abstract.NodeLegalComp (NodeWit WitLegal NonExnLegal)
open Silmaril.Wasm.Cfg.CfgInst (LegalRes legalSemD InstDom)
open Silmaril.Wasm.Cfg.CfgLegal (cfgSemD)
open Silmaril.Wasm.Cfg.SessionCheck (CompIn)
open Silmaril.Wasm.Component (Comp CoreIface sigU)
open Silmaril.Wasm.Component.Reference (NumInstance)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- **`LegalRes` allows every non-exception result at every store.** -/
theorem nonExnLegal_legalRes : NonExnLegal LegalRes :=
  fun _ _ hr a ha => absurd ha (hr a)

/-! ## Legality of every hidden interaction -/

/-- **Every hidden interaction of a node is legal at every importer point.** -/
theorem nodeHidLegal (P : Numerics.Profile) (m : NumInstance) : NodeHidLegal P m :=
  fun _ _ _ _ _ h => Abstract.NodeLegalComp.witLegal_of_nodeWit nonExnLegal_legalRes h

/-- **Every hidden node interaction of every component is legal at every importer point.** -/
theorem compLegal (P : Numerics.Profile) (c : Comp NumInstance) : CompLegal P c :=
  Silmaril.Proofs.Wasm.Cfg.CfgLegalComp.compIn_of_forall (nodeHidLegal P) c

variable {o : GrowOracle}

/-! ## `legalSemD = core3SemD` -/

/-- **The `legalSemD` node is the `core3SemD` node.** -/
theorem legalSemD_sem_eq (m : NumInstance) :
    (legalSemD (profile o)).sem m = (core3SemD (profile o)).sem m :=
  Abstract.NodeLegalComp.semOfSD_instTripleQ_eq nonExnLegal_legalRes m m.inst.store

/-- **`legalSemD (profile o) = core3SemD (profile o)`.** -/
theorem legalSemD_eq : legalSemD (profile o) = core3SemD (profile o) := by
  show (⟨_⟩ : Component.DCoreSem NumInstance) = ⟨_⟩
  exact congrArg Component.DCoreSem.mk (funext legalSemD_sem_eq)

/-- **Exact component legality**: equal denotations, for every component. -/
theorem denUD_legalSemD_eq (c : Comp NumInstance) :
    c.denUD (legalSemD (profile o)) = c.denUD (core3SemD (profile o)) := by
  rw [legalSemD_eq]

/-- Equal denotations at the interface signatures. -/
theorem denD_legalSemD_eq (c : Comp NumInstance) :
    c.denD (legalSemD (profile o)) = c.denD (core3SemD (profile o)) := by
  rw [legalSemD_eq]

/-- **Finite plays**: those of `core3SemD` whose hidden node interactions are legal. -/
theorem mem_denUD_legalSemD_iff (c : Comp NumInstance) {p : List (Move sigU sigU)} :
    p ∈ (c.denUD (legalSemD (profile o))).toStrategy ↔
      p ∈ (c.denUD (core3SemD (profile o))).toStrategy ∧ CompLegal (profile o) c := by
  rw [denUD_legalSemD_eq]
  exact ⟨fun h => ⟨h, compLegal _ c⟩, And.left⟩

/-- **Pending calls**: plays ending in a call below, as for finite plays. -/
theorem pending_denUD_legalSemD_iff (c : Comp NumInstance) {p : List (Move sigU sigU)}
    {e : sigU.Op} :
    p ++ [.inl (.ask e)] ∈ (c.denUD (legalSemD (profile o))).toStrategy ↔
      p ++ [.inl (.ask e)] ∈ (c.denUD (core3SemD (profile o))).toStrategy ∧
        CompLegal (profile o) c :=
  mem_denUD_legalSemD_iff c

/-- **Divergences, hidden chatter included**: those of `core3SemD` whose hidden node interactions
are legal. -/
theorem div_denUD_legalSemD_iff (c : Comp NumInstance) {p : List (Move sigU sigU)} :
    p ∈ (c.denUD (legalSemD (profile o))).div ↔
      p ∈ (c.denUD (core3SemD (profile o))).div ∧ CompLegal (profile o) c := by
  rw [denUD_legalSemD_eq]
  exact ⟨fun h => ⟨h, compLegal _ c⟩, And.left⟩

/-- **Infinite plays**: those of `core3SemD` whose hidden node interactions are legal. -/
theorem inf_denUD_legalSemD_iff (c : Comp NumInstance) {J : Set (List (Move sigU sigU))} :
    J ∈ (c.denUD (legalSemD (profile o))).inf ↔
      J ∈ (c.denUD (core3SemD (profile o))).inf ∧ CompLegal (profile o) c := by
  rw [denUD_legalSemD_eq]
  exact ⟨fun h => ⟨h, compLegal _ c⟩, And.left⟩

/-! ## Node-level forms with witnesses -/

/-- **Finite plays of a `legalSemD` node**: a hidden interaction legal at every importer
point. -/
theorem mem_legalSemD_sem_iff {m : NumInstance}
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ ((legalSemD (profile o)).sem m).toStrategy ↔
      ∃ u v a b, NodeWit (profile o) m m.inst.store p u v a b ∧
        WitLegal (profile o) LegalRes m m.inst.store a :=
  Abstract.NodeLegalComp.mem_semOfSD_instTripleQ_iff nonExnLegal_legalRes

/-- **Divergences of a `legalSemD` node**: a hidden interaction whose instance play is a
divergence legal at every importer point. -/
theorem div_legalSemD_sem_iff {m : NumInstance}
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ ((legalSemD (profile o)).sem m).div ↔
      ∃ u v a b, NodeWit (profile o) m m.inst.store p u v a b ∧
        a ∈ (spullD (instSession m.inst (profile o) m.inst.store)).div ∧
        WitLegal (profile o) LegalRes m m.inst.store a :=
  Abstract.NodeLegalComp.div_semOfSD_instTripleQ_iff nonExnLegal_legalRes

/-- **Infinite plays of a `legalSemD` node** are those of the `core3SemD` node (the reverse
coercion direction included); see `NodeLegalComp.inf_inner_lift` for the coherent witness. -/
theorem inf_legalSemD_sem_iff {m : NumInstance}
    {J : Set (List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports)))} :
    J ∈ ((legalSemD (profile o)).sem m).inf ↔ J ∈ ((core3SemD (profile o)).sem m).inf := by
  rw [legalSemD_sem_eq]

/-! ## The CFG-built component semantics -/

/-- **On an instance of the CFG domain, the CFG-built node is the `core3SemD` node.** -/
theorem cfgSemD_sem_eq_core3 {m : NumInstance} (hm : InstDom m.inst m.inst.store) :
    cfgSemD.sem m = (core3SemD (profile o)).sem m := by
  rw [CfgLegal.cfgSemD_sem_eq (o := o) hm, legalSemD_sem_eq]

/-- **The CFG-built denotation is the `core3SemD` denotation** on components whose core instances
are in the CFG domain. -/
theorem denUD_cfgSemD_eq_core3 (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => InstDom m.inst m.inst.store) c) :
    c.denUD cfgSemD = c.denUD (core3SemD (profile o)) := by
  rw [CfgLegal.denUD_cfgSemD_eq (o := o) c hc, denUD_legalSemD_eq]

/-- The same at the interface signatures. -/
theorem denD_cfgSemD_eq_core3 (c : Comp NumInstance)
    (hc : CompIn (fun m : NumInstance => InstDom m.inst m.inst.store) c) :
    c.denD cfgSemD = c.denD (core3SemD (profile o)) := by
  unfold Comp.denD
  rw [denUD_cfgSemD_eq_core3 (o := o) c hc]

end Silmaril.Wasm.Cfg.CfgLegalComp
