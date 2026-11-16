module

public import Silmaril.Wasm.Abstract.LegalStrat.Defs
public import Silmaril.Wasm.Abstract.BodyStrat.Thms
public import Silmaril.Wasm.Abstract.LegalFunctor.Thms
import Silmaril.Proofs.Wasm.Abstract.LegalStrat.Basic

/-!
# Wasm legality for the canonical play object: theorems

**1. Legality is #623's legal oracles, answer by answer.**

* `legal_iff`: `LegalFunctor.Legal Γ C` (`ArityResp Γ (fitP C)`) holds exactly when every answer
  `C` gives is a `LegalAns`. So the legal oracles are the oracles answering only `wasmL Γ`-legally,
  and `legalC Γ` (every legal answer) is the largest of them (`legal_legalC`);
* `legalLog_of`: a log answered by a legal oracle is a legal log.

**2. Injection** (`toDStratBodyL_denL_eq_iff`). On the legal interface `wasmL Γ`, two code lists
have the same play object exactly when they are `OpEquivPL Γ`: the same logged non-trap outcomes,
traps and pending calls at every legal log. Proved through `BodyStrat.toDStratBodyL_eq_iff`
(equal legal play objects is equal restricted triples), then, as for
`BodyStrat.toDStratBody_denL_iff`, by reading paths and pending calls of the exposed body as
logged runs at the universal oracle (`FunctorP.evalLXP_iff`, `evalLXP_trap_iff`,
`reachXP_iff_pend`). The divergent and infinite components of the restricted triple add nothing:
a silent divergence at a legal log is a reachable node with neither a value nor a pending call,
and an infinite stream with legal answers is a limit of legal pending prefixes. `OpEquivPL` is
defined from logged runs, not from the play object.

**3. Links.**

* `opEquivP_le_opEquivPL`: `OpEquivP` (every log) implies `OpEquivPL` (legal logs);
* `opEquivL_of_opEquivPL`: `OpEquivPL Γ es es'` implies #623's `OpEquivL Γ I es es'`, at every
  interface `I` (world interfaces in particular). An `EvalOXP` run under a legal oracle is a logged
  run whose log the oracle answered (`FunctorP.evalOXP_iff_log`), hence a legal log. So legal-play
  equality determines the image of `es` under #623's `legalFunctor`
  (`LegalFunctor.legalFunctor_map_eq_iff`).
* **The converse is not claimed**, and fails in general: `OpEquivL` compares answered runs with
  their logs forgotten, only from the world states of `I`, while `OpEquivPL` compares logs, pending
  calls and every initial state.

**4. Checked code in legal plays** (`evalLXP_lands_legal`). For typed checked code
`THom Γ I J es` from a world state of `I`, a logged fallthrough whose log is legal lands in a
world state of `J`, under any oracle: the legal log is a run of the legal oracle `legalC Γ`, and
#623's `thom_lands_legal` applies. This is stated for finished fallthroughs only. That the
*pending* calls of a legally answered prefix are fitting calls from world stores (arguments of
the callee's parameter count) is not proved here: it needs the checker's invariant carried to
every call site of a `ReachXP` prefix, which `TypedCatFit` proves only for finished runs.

**Scope.** The supported checked fragment (the checker's integer, control, call and exception
forms), not full Wasm. Equal legal play objects is `OpEquivPL`; this is not contextual full
abstraction. No host-level Core faithfulness is claimed. The observed call events are those
`denL` already exposes: no internal call-graph observability is added.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.LegalStrat`.
-/

public section

namespace Silmaril.Wasm.Abstract.LegalStrat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.StoreCall (Answered)
open Silmaril.Wasm.Abstract.ExposePStruct (Ctx denL)
open Silmaril.Wasm.Abstract.ExposePTyped (TIface THom)
open Silmaril.Wasm.Abstract.WorldFunctor (WSt)
open Silmaril.Wasm.Abstract.LegalFunctor (Legal OpEquivL)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Abstract.FunctorP (ACall EvalLXP OpEquivP)
open Silmaril.Wasm.Abstract.BodyStrat (toDStratBodyL)

variable {H : Type}

/-! ## 1. Legal oracles -/

/-- **Legal oracles answer legally**: `Legal Γ C` exactly when every answer of `C` is legal. -/
theorem legal_iff {Γ : Ctx H} {C : CallRel H} :
    Legal Γ C ↔ ∀ s a args ans, C s a args ans → LegalAns Γ s a args ans :=
  Silmaril.Proofs.Wasm.Abstract.LegalStrat.legal_iff

/-- The largest legal oracle is legal. -/
theorem legal_legalC (Γ : Ctx H) : Legal Γ (legalC Γ) :=
  Silmaril.Proofs.Wasm.Abstract.LegalStrat.legal_legalC Γ

/-- A log answered by a legal oracle is legal. -/
theorem legalLog_of {Γ : Ctx H} {C : CallRel H} (hC : Legal Γ C) {cs : List (ACall H)}
    (hA : Answered C cs) : LegalLog Γ cs :=
  Silmaril.Proofs.Wasm.Abstract.LegalStrat.legalLog_of hC hA

/-- A legal log is a log answered by the largest legal oracle. -/
theorem legalLog_iff_answered {Γ : Ctx H} {cs : List (ACall H)} :
    LegalLog Γ cs ↔ Answered (legalC Γ) cs :=
  Iff.rfl

/-! ## 2. Injection -/

/-- **The legal play object is faithful for the legal operational equivalence.** -/
theorem toDStratBodyL_denL_eq_iff (Γ : Ctx H) (es es' : List BExpr) :
    toDStratBodyL (wasmL Γ) (denL es) = toDStratBodyL (wasmL Γ) (denL es') ↔
      OpEquivPL Γ es es' :=
  (BodyStrat.toDStratBodyL_eq_iff _ _ _).trans
    (Silmaril.Proofs.Wasm.Abstract.LegalStrat.restrict_denL_iff Γ es es')

/-! ## 3. Links -/

/-- Exact operational equivalence implies the legal one. -/
theorem opEquivP_le_opEquivPL (Γ : Ctx H) {es es' : List BExpr} (h : OpEquivP H es es') :
    OpEquivPL Γ es es' :=
  fun C s f stk cs _ => h C s f stk cs

/-- **Legal-play equality determines #623's answered runs under legal oracles**, at every
interface. -/
theorem opEquivL_of_opEquivPL {Γ : Ctx H} (I : TIface) {es es' : List BExpr}
    (h : OpEquivPL Γ es es') : OpEquivL Γ I es es' :=
  Silmaril.Proofs.Wasm.Abstract.LegalStrat.opEquivL_of_opEquivPL I h

/-- Equal legal play objects give #623's equivalence. -/
theorem opEquivL_of_toDStratBodyL_eq {Γ : Ctx H} (I : TIface) {es es' : List BExpr}
    (h : toDStratBodyL (wasmL Γ) (denL es) = toDStratBodyL (wasmL Γ) (denL es')) :
    OpEquivL Γ I es es' :=
  opEquivL_of_opEquivPL I ((toDStratBodyL_denL_eq_iff Γ es es').1 h)

/-! ## 4. Checked code in legal plays -/

/-- **Legally answered logged fallthroughs of typed code land in the world**, under any oracle. -/
theorem evalLXP_lands_legal {Γ : Ctx H} {I J : TIface} {es : List BExpr} (hm : THom Γ I J es)
    {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val} (hw : WSt Γ I s f stk)
    {cs : List (ACall H)} (hcs : LegalLog Γ cs) {s' : Store H} {f' : Frame} {vs : List Val}
    (d : EvalLXP C s f stk es cs (s', f', .flow (.normal vs))) : WSt Γ J s' f' vs :=
  Silmaril.Proofs.Wasm.Abstract.LegalStrat.evalLXP_lands_legal hm hw hcs d

end Silmaril.Wasm.Abstract.LegalStrat
