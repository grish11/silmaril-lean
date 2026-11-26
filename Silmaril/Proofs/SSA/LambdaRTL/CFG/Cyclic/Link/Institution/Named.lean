module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Named

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement (resumeRTL_eq_resumeSSA)

variable {V F α : Type} [DecidableEq V] [Inhabited V] {a b : Nat}

theorem namedRTL_closed (graph : Graph V F a b) (port : Fin a) :
    RoundTrip.PacketClosed (graph.namedRTL port) := by
  intro item member
  obtain ⟨source, listed, rfl⟩ := List.mem_map.mp member
  simpa only [Block.relabel, Graph.body_fv_relabel] using graph.table_closed source listed

private theorem widen_injective {n b : Nat} :
    Function.Injective (Sum.map Fin.val id : Label n b → NamedLabel b) := by
  intro left right equal
  cases left <;> cases right <;> simp_all [Fin.ext_iff]

theorem namedRTL_observe (model : PairModel F Part α) (graph : Graph V F a b)
    (port : Fin a) (store : V → α) :
    rtlObserve model (graph.namedRTL port) store = publicResult <$> graph.denote model.val (port, store default) := by
  let start : Transfer V (NamedLabel b) α := (Sum.map Fin.val id (graph.entry port), store default, store)
  have viaTable : rtlObserve model (graph.namedRTL port) store =
      Cyclic.runSSA model.val (graph.namedRTL port) store := by
    have launch : (graph.namedRTL port).entry.evalJump model.val store = pure (obs start) := rfl
    rw [Cyclic.runSSA, launch, pure_bind]
    exact resumeRTL_eq_resumeSSA model.val _ (namedRTL_closed graph port) store start
  have seed : upd store default (store default) = store := by
    funext name
    by_cases same : name = default <;> simp [upd, same]
  have run := graph.denote_eq_runSSA_relabel model.val (Sum.map Fin.val id) widen_injective
    store port (store default)
  rw [seed] at run
  exact viaTable.trans run.symm

theorem publicResult_le_iff (lhs rhs : Part (Fin b × α)) :
    (publicResult <$> lhs : Part (NamedLabel b × α)) ≤ publicResult <$> rhs ↔ lhs ≤ rhs := by
  constructor
  · intro included result member
    obtain ⟨other, present, equal⟩ :=
      (Part.mem_map_iff publicResult).mp (included _ (Part.mem_map publicResult member))
    have same : other = result := Prod.ext (Sum.inr.inj (congrArg Prod.fst equal))
      (congrArg (fun output : NamedLabel b × α => output.2) equal)
    exact same ▸ present
  · intro included result member
    obtain ⟨source, present, rfl⟩ := (Part.mem_map_iff publicResult).mp member
    exact Part.mem_map publicResult (included _ present)

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Named
