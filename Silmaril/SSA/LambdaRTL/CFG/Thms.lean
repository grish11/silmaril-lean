module

public import Silmaril.SSA.LambdaRTL.CFG.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Correctness

/-!
# Flat three-address CFGs for acyclic λRTL: checked results

* `run_flatten`: the flattening of a dominator-tree region runs exactly as the region under the
  λRTL store semantics, with free labels embedded as exits.
* `run_eq_toRegion`: every forward CFG runs as its reading-back region `CFG.toRegion`.
* `run_relabel`: running commutes with relabelling injective on all syntactic labels.
* `run_relabel_of_check`: a checked relabelling preserves lookup in every forward suffix and
  may identify distinct exit-only labels.
* `run_of_validate`: **validator soundness** — if `validate exit r g = true` then `g` runs as
  `r` (exits renamed by `exit`) in every model and every lawful monad.

Scope: acyclic (forward-only jumps; a backward jump is an exit). The validator is syntactic
(flattening up to relabelling), so it is complete only for CFGs of that shape.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG

universe v w

section MapOp

variable {V K : Type w} {F F' F'' : Type v}

theorem Body.toRegion_mapOp (h : F → F') (body : Body V K F) :
    (body.mapOp h).toRegion = body.toRegion.mapOp h :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.Body.toRegion_mapOp h body

theorem mapOp_id (graph : CFG V K F) : graph.mapOp id = graph :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.mapOp_id graph

theorem mapOp_comp (h : F → F') (k : F' → F'') (graph : CFG V K F) :
    graph.mapOp (k ∘ h) = (graph.mapOp h).mapOp k :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.mapOp_comp h k graph

end MapOp

variable {V L K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w} [Monad M]
  [LawfulMonad M] [DecidableEq V] [DecidableEq L] [DecidableEq K]

/-- A body executes as its region, followed by a continuation on the exit. -/
theorem Body.exec_eq_evalRTL {R : Type w} (model : Model F M α) (next : K → α → (V → α) → M R)
    (body : Body V K F) (store : V → α) :
    body.exec model next store =
      body.toRegion.evalRTL model store >>= fun out => next out.1 out.2.1 out.2.2 :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.Body.exec_eq model next body store

theorem run_flatten (m : Model F M α) (r : Region V L F) (σ : V → α) :
    (flatten r).run m σ = (fun e => (Sum.inl e.1, e.2)) <$> r.evalRTL m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.run_flatten m r σ

theorem run_eq_toRegion (m : Model F M α) (g : CFG V K F) (σ : V → α) :
    g.run m σ = g.toRegion.evalRTL m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.run_eq_toRegion m g σ

theorem run_relabel {K' : Type w} [DecidableEq K'] (m : Model F M α) (π : K → K')
    (g : CFG V K F) (hinj : ∀ a ∈ g.labels, ∀ b ∈ g.labels, π a = π b → a = b) (σ : V → α) :
    (g.relabel π).run m σ = (fun e => (π e.1, e.2)) <$> g.run m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.run_relabel m π g hinj σ

/-- Rename the exit while preserving the payload, entire final store and monadic outcome.
The check preserves each equality test between any syntactic target and any block label. -/
theorem run_relabel_of_check {K' : Type w} [DecidableEq K'] (m : Model F M α) (rename : K → K')
    (graph : CFG V K F) (σ : V → α) (accepted : graph.relabelLookupCheck rename = true) :
    (graph.relabel rename).run m σ = (fun out => (rename out.1, out.2)) <$> graph.run m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.run_relabel_of_check m rename graph σ accepted

theorem run_of_validate [DecidableEq F] [Inhabited K] (m : Model F M α) (exit : L → K)
    (r : Region V L F) (g : CFG V K F) (h : validate exit r g = true) (σ : V → α) :
    g.run m σ = (fun e => (exit e.1, e.2)) <$> r.evalRTL m σ :=
  Silmaril.Proofs.SSA.LambdaRTL.CFG.run_of_validate m exit r g h σ

end Silmaril.SSA.LambdaRTL.CFG
