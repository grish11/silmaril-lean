module

public import Silmaril.Wasm.Abstract.NodeLegalComp.Defs
public import Silmaril.Wasm.Abstract.NodeLegal.Thms
public import Silmaril.Wasm.Abstract.NodeDiv.Thms
public import Silmaril.Games.DivCompAns.Thms
import Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.Basic

/-!
# Host-answer domains through the component coercions: theorems

For a host-answer domain `Q` that allows every non-exception result at every store
(`NonExnLegal Q`; e.g. `Cfg.CfgInst.LegalRes`):

**The boundary.** `importH m` (the import coercion of `semOfSD m`, hence of every
`core3SemD`/`legalSemD` node) answers each import call `e` with `payloadAnswer _ r`, which is
`.values` or `.trap` and never `.throw` (`toResult_payloadAnswer_ne`). So every answer it gives is
allowed by `Q` at **every** store (`answersIn_importH`), in particular at the store of the
importer's hidden `.waiting` state. This is the only path by which an instance of `semOfSD m σ`
receives import answers, whatever `σ`, and whatever surrounds the node (wiring `implsN`, `ext`,
nested instances, hidden composition): those act on the node's interface
`CoreIface.sig m.imports`, above `importH m`.

**Exactness at the node interface.**

* `ansPart_threadS_instTripleQ` (`profile o`): the restricted session is the part of the
  instance session answered legally at every store, on all observations.
* `semOfSD_eq_of_ansPart`, `semOfSD_instTripleQ_eq` (`profile o`):
  `semOfSD m (threadS (instTripleQ m.inst (profile o) Q) s₀) = semOfSD m (instSession …)`, on
  finite plays, divergences (local, and hidden chatter, through the generic
  `DStrategy.comp_eq_of_ansPart`) and infinite plays.
* `witLegal_of_nodeWit`: **every** hidden interaction of the node (any profile) has a hidden
  instance play legal at every importer point, its end included (`NodeLegal.LegalPlayD`).
* `mem_semOfSD_instTripleQ_iff`, `div_semOfSD_instTripleQ_iff`: the plays (divergences) of the
  restricted node are exactly those with a hidden interaction legal at every importer point.
* `inf_semOfSD_instTripleQ_iff`, `inf_inner_lift`: infinite plays; when the instance side of an
  infinite node interaction moves forever, its limit is the limit of **one** coherent inner
  infinite interaction all of whose hidden instance stages are legal.

**Not claimed.** On the session interface `ssig` (before `importH`), environments may answer
`throw a`; the restricted session drops the dangling ones. Nothing here relates the unrestricted
session to a CFG reading on such environments.
-/

public section

namespace Silmaril.Wasm.Abstract.NodeLegalComp

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratSession (threadS)
open Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.InstSession (ssig instSession spullD srelabel semOfSD)
open Silmaril.Wasm.Abstract.NodeLegal (instTripleQ RoundLegal LegalPlay LegalPlayD)
open Silmaril.Wasm.Component (CoreIface Payload)
open Silmaril.Wasm.Component.Reference (NumInstance importH exportH payloadAnswer)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Numerics (Profile)

variable {I : ScalarInstance} {Q : Store Nat → Result → Prop}

/-! ## Answers legal at every store -/

/-- A log of answers legal at every store is legal in its round. -/
theorem roundLegal_of {P : Profile} {s : Store Nat} {a : I.F.Op} {c : List (Call I.E)}
    (h : ∀ x ∈ c, AnsLegal I Q x.1 x.2) : RoundLegal I P Q s a c :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.roundLegal_of h

/-- **A play whose import answers are legal at every store is legal**, its end included. -/
theorem legalPlayD_of_lAnsIn {P : Profile} {s₀ : Store Nat}
    {q : List (Move I.E (ssig I.exports))} (hq : LAnsIn (AnsLegal I Q) q) :
    LegalPlayD I P Q s₀ q :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.legalPlayD_of_lAnsIn hq

/-- **`payloadAnswer` is never an exception.** -/
theorem toResult_payloadAnswer_ne (ft : FnType) (r : Option Payload) (a : Nat) :
    (payloadAnswer ft r).toResult ≠ .throw a :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.toResult_payloadAnswer_ne ft r a

/-- **`importH m` answers every import call legally at every store.** -/
theorem answersIn_importH (hQ : NonExnLegal Q) (m : NumInstance) :
    (DStrategy.ofHandler (importH m)).AnswersIn (AnsLegal m.inst Q) :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.answersIn_importH hQ m

/-- The read-back on `ifaceSig` keeps the part answered in `R`. -/
theorem ansPart_spullD {E : Sig.{0}} {ts : List FnType} {R : (m : E.Op) → E.Ar m → Prop}
    {σ' σ : DStrategy E (ssig ts)} (h : σ'.AnsPart R σ) : (spullD σ').AnsPart R (spullD σ) :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.ansPart_spullD h

/-! ## Exactness at the node interface -/

/-- **The restricted session is the part of the instance session answered legally at every
store.** -/
theorem ansPart_threadS_instTripleQ {o : GrowOracle} (s₀ : Store Nat) :
    (threadS (instTripleQ I (profile o) Q) s₀).AnsPart (AnsLegal I Q)
      (instSession I (profile o) s₀) :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.ansPart_threadS_instTripleQ s₀

/-- **The node only sees the part of a session answered legally at every store.** -/
theorem semOfSD_eq_of_ansPart (hQ : NonExnLegal Q) {m : NumInstance}
    {σ' σ : DStrategy m.inst.E (ssig m.inst.exports)} (h : σ'.AnsPart (AnsLegal m.inst Q) σ) :
    semOfSD m σ' = semOfSD m σ :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.semOfSD_eq_of_ansPart hQ h

/-- **The restricted node is the instance node**, on every observation. -/
theorem semOfSD_instTripleQ_eq {o : GrowOracle} (hQ : NonExnLegal Q) (m : NumInstance)
    (s₀ : Store Nat) :
    semOfSD m (threadS (instTripleQ m.inst (profile o) Q) s₀) =
      semOfSD m (instSession m.inst (profile o) s₀) :=
  semOfSD_eq_of_ansPart hQ (ansPart_threadS_instTripleQ s₀)

/-- **Every hidden interaction of a node is legal at every importer point.** -/
theorem witLegal_of_nodeWit (hQ : NonExnLegal Q) {P : Profile} {m : NumInstance}
    {s₀ : Store Nat} {p u v a b} (h : NodeWit P m s₀ p u v a b) : WitLegal P Q m s₀ a :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.witLegal_of_nodeWit hQ h

variable {o : GrowOracle}

/-- **Finite plays of the restricted node**: exactly those with a hidden interaction legal at
every importer point. -/
theorem mem_semOfSD_instTripleQ_iff (hQ : NonExnLegal Q) {m : NumInstance} {s₀ : Store Nat}
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ (semOfSD m (threadS (instTripleQ m.inst (profile o) Q) s₀)).toStrategy ↔
      ∃ u v a b, NodeWit (profile o) m s₀ p u v a b ∧ WitLegal (profile o) Q m s₀ a := by
  rw [semOfSD_instTripleQ_eq hQ]
  constructor
  · rintro ⟨u, hu, v, ⟨a, ha, b, hb, hab⟩, huv⟩
    have w : NodeWit (profile o) m s₀ p u v a b := ⟨hu, huv, hab, ha, hb⟩
    exact ⟨u, v, a, b, w, witLegal_of_nodeWit hQ w⟩
  · rintro ⟨u, v, a, b, ⟨hu, huv, hab, ha, hb⟩, -⟩
    exact ⟨u, hu, v, ⟨a, ha, b, hb, hab⟩, huv⟩

/-- **Divergences of the restricted node**: exactly those with a hidden interaction whose
instance play is a divergence legal at every importer point (the coercions add no chatter,
`NodeDiv.div_semOfSD`). -/
theorem div_semOfSD_instTripleQ_iff (hQ : NonExnLegal Q) {m : NumInstance} {s₀ : Store Nat}
    {p : List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports))} :
    p ∈ (semOfSD m (threadS (instTripleQ m.inst (profile o) Q) s₀)).div ↔
      ∃ u v a b, NodeWit (profile o) m s₀ p u v a b ∧
        a ∈ (spullD (instSession m.inst (profile o) s₀)).div ∧ WitLegal (profile o) Q m s₀ a := by
  rw [semOfSD_instTripleQ_eq hQ, NodeDiv.div_semOfSD]
  constructor
  · rintro ⟨u, v, huv, hu, a, b, hab, ha, hb⟩
    have w : NodeWit (profile o) m s₀ p u v a b := ⟨hu, huv, hab, (spullD _).div_mem ha, hb⟩
    exact ⟨u, v, a, b, w, ha, witLegal_of_nodeWit hQ w⟩
  · rintro ⟨u, v, a, b, ⟨hu, huv, hab, -, hb⟩, ha, -⟩
    exact ⟨u, v, huv, hu, a, b, hab, ha, hb⟩

/-- **Infinite plays of the restricted node** are those of the instance node; each infinite
interaction of one is an infinite interaction of the other with the same chains
(`InfInteraction.ansRight`, `InfInteraction.ofLe`). -/
theorem inf_semOfSD_instTripleQ_iff (hQ : NonExnLegal Q) {m : NumInstance} {s₀ : Store Nat}
    {J : Set (List (Move (CoreIface.sig m.imports) (CoreIface.sig m.exports)))} :
    J ∈ (semOfSD m (threadS (instTripleQ m.inst (profile o) Q) s₀)).inf ↔
      J ∈ (semOfSD m (instSession m.inst (profile o) s₀)).inf := by
  rw [semOfSD_instTripleQ_eq hQ]

/-- **The coherent hidden interaction of an infinite node play**: when the instance side of an
infinite node interaction moves forever, its limit is the limit of one inner infinite interaction
of the read-back instance session with `exportH m` whose stages answer legally at every store and
whose hidden instance plays are all legal at every importer point. -/
theorem inf_inner_lift (hQ : NonExnLegal Q) {P : Profile} {m : NumInstance} {s₀ : Store Nat}
    (i : DStrategy.InfInteraction (DStrategy.ofHandler (importH m))
      ((spullD (instSession m.inst P s₀)).comp (DStrategy.ofHandler (exportH m))))
    (hu : i.t.Unbounded) :
    ∃ j : DStrategy.InfInteraction (spullD (instSession m.inst P s₀))
        (DStrategy.ofHandler (exportH m)),
      j.p.Unbounded ∧ j.p.lim = i.t.lim ∧ (∀ n, LAnsIn (AnsLegal m.inst Q) (j.p n)) ∧
        ∀ n, WitLegal P Q m s₀ (j.s n) :=
  Silmaril.Proofs.Wasm.Abstract.NodeLegalComp.inf_inner_lift hQ i hu

end Silmaril.Wasm.Abstract.NodeLegalComp
