module

public import Silmaril.Wasm.Region.Defs
public import Silmaril.Wasm.Cfg.Machine.Thms

/-! # Operational allowances over the existing Wasm block CFG

The syntactic inventory is unchanged. Every root block additionally allows a
trap, since the operational theorem does not require typing. Nested blocks use
Top until a handler-coverage certificate is supplied: catch edges belong to an
ancestor `try_table`, not necessarily the throwing block's adjacency list.
Calls and unresolved handlers retain the existing Top policy.
-/

@[expose] public section
namespace Silmaril.Wasm.Region
open Silmaril.Semantics.Region

def operationalTargets (body : Expr) (b : Cfg.BlockId) (s : Cfg.Segment) : Targets Cfg.Target :=
  if b.seq = [] then
    match candidateTargets body b s with
    | .top => .top
    | .finite xs => .finite (insert .trap xs)
  else .top

/-- Same block inventory, with allowances proved to cover machine steps.
A row alone does not certify admission, whole-region coverage or termination. -/
def operationalCandidates (functionIndex : Nat) (body : Expr) : List CandidateRow :=
  (Cfg.blocks body).map fun (b, s) =>
    ⟨functionIndex, b, operationalTargets body b s, Cfg.blockEffects body b s⟩

/-- Region queries over the existing block machine, with its fixed profile and
call oracle. Synthetic exit/trap/raise are distinguished halts. Unanswered
calls can be stuck; they are never invented resumptions. The empty event
alphabet observes control and final state, not an interprocedural effect trace. -/
def system {H : Type} (P : Numerics.Profile) (host : Execution.Core.HostSemantics H)
    (C : Abstract.CallRel H) (body : Expr) :
    TransitionSystem (Cfg.Machine.MState H) Cfg.Target Empty Cfg.Target where
  pc st := st.node
  step st es st' := es = [] ∧ Cfg.Machine.MStepC P host C body st st'
  halt st target := st.node = target ∧ target.IsSink

end Silmaril.Wasm.Region
