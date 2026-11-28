module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Thms

/-! Refining a write-safe map's input can only remove executable occurrence marks. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Proofs

open SeaOfNodes.Diamond (Val ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleLE tupleFacts)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.Loop.SCCP (BankFacts BankDecidableEq bankTuple bankTuple_tupleFacts)
open SeaOfNodes.MLIR (Word)
open Semantics.Dataflow (Flat)
open Semantics.Dataflow.FiniteHeight (HeightBound)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Port Tuple)
open Identification (BankMap PortMap SafeWrites pull pull_get program pushFacts blockFacts_pull)
open SCCP (Marked State gate incomingIndex exitIndex blockFacts)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {S T : EntrySignature} {out : ValueSort Width}

private theorem read_join {ports : List (Diamond.Ty Width)} {t : Diamond.Ty Width} (port : Port ports t)
    (eqs : ∀ i : Fin ports.length, DecidableEq (Val Word ports[i]))
    (a b : BankFacts Word ports) [equal : DecidableEq (Val Word t)] :
    (bankTuple (fun i => @Flat.join _ (eqs i) (a i) (b i))).get port =
      Flat.join ((bankTuple a).get port) ((bankTuple b).get port) := by
  induction port generalizing equal with
  | head =>
    change @Flat.join _ (eqs 0) (a 0) (b 0) = @Flat.join _ equal (a 0) (b 0)
    exact congrArg (fun eq => @Flat.join _ eq (a 0) (b 0)) (Subsingleton.elim (eqs 0) equal)
  | tail p ih => exact ih (fun i => eqs i.succ) (fun i => a i.succ) (fun i => b i.succ)

private theorem read_gate {ports : List (Diamond.Ty Width)} {t : Diamond.Ty Width} (port : Port ports t)
    (marks : Marked) (edge : Fin 4) (bank : BankFacts Word ports) :
    (bankTuple (fun i => gate marks edge (bank i))).get port =
      gate marks edge ((bankTuple bank).get port) := by
  by_cases marked : edge ∈ marks
  · simp only [gate, marked, ite_true]
  · simp only [gate, marked, ite_false]
    induction port with
    | head => rfl
    | tail _ ih => exact ih (fun i => bank i.succ)

private theorem read_phi {regs : List (ValueSort Width)} [equal : BankDecidableEq Word (dataPorts regs)]
    (marks : Marked) (columns : Incoming → BankFacts Word (dataPorts regs))
    {t : Diamond.Ty Width} (port : Port (dataPorts regs) t) [DecidableEq (Val Word t)] :
    (bankTuple (SCCP.phiFacts marks columns)).get port =
      (gate marks (incomingIndex .entry) ((bankTuple (columns .entry)).get port) ⊔
        gate marks (incomingIndex (.feedback true)) ((bankTuple (columns (.feedback true))).get port)) ⊔
      gate marks (incomingIndex (.feedback false)) ((bankTuple (columns (.feedback false))).get port) := by
  unfold SCCP.phiFacts
  change (bankTuple (fun i => @Flat.join _ (equal.atPort i)
    (@Flat.join _ (equal.atPort i) (gate marks (incomingIndex .entry) (columns .entry i))
      (gate marks (incomingIndex (.feedback true)) (columns (.feedback true) i)))
    (gate marks (incomingIndex (.feedback false)) (columns (.feedback false) i)))).get port = _
  rw [read_join, read_join, read_gate, read_gate, read_gate]
  rfl

private theorem read_phi_le {regs : List (ValueSort Width)} [BankDecidableEq Word (dataPorts regs)]
    (marks : Marked) (columns : Incoming → BankFacts Word (dataPorts regs))
    {t : Diamond.Ty Width} (port : Port (dataPorts regs) t) (upper : Fact Word t) :
    (bankTuple (SCCP.phiFacts marks columns)).get port ≤ upper ↔
      ∀ edge, incomingIndex edge ∈ marks → (bankTuple (columns edge)).get port ≤ upper := by
  classical
  rw [read_phi, sup_le_iff, sup_le_iff]
  have gated (edge : Incoming) :
      gate marks (incomingIndex edge) ((bankTuple (columns edge)).get port) ≤ upper ↔
        (incomingIndex edge ∈ marks → (bankTuple (columns edge)).get port ≤ upper) := by
    by_cases active : incomingIndex edge ∈ marks <;> simp [gate, active]
  simp only [gated]
  constructor
  · rintro ⟨⟨entry, yes⟩, no⟩ edge
    cases edge with
    | entry => exact entry
    | feedback side => cases side <;> assumption
  · intro bounded
    exact ⟨⟨bounded .entry, bounded (.feedback true)⟩, bounded (.feedback false)⟩

private def Refines (map : PortMap S T) (fine : State Word T.regs out) (coarse : State Word S.regs out) : Prop :=
  fine.1 ⊆ coarse.1 ∧ TupleLE (pull map (bankTuple fine.2.1)) (bankTuple coarse.2.1)

private theorem refines_bottom (map : PortMap S T) (upper : State Word S.regs out) :
    Refines map ⊥ upper := by
  refine ⟨Finset.empty_subset _, ?_⟩
  intro t port
  rw [pull_get]
  have bottomRead {ports : List (Diamond.Ty Width)} {t : Diamond.Ty Width} (p : Port ports t) :
      (bankTuple (⊥ : BankFacts Word ports)).get p = ⊥ := by
    induction p with
    | head => rfl
    | tail _ ih => exact ih
  rw [show (⊥ : State Word T.regs out).2.1 = ⊥ from rfl, bottomRead]
  exact bot_le

private theorem transfer_refines (map : PortMap S T) (p : Program Op S.regs out)
    (safe : SafeWrites map p) (original : EntryFacts S.regs) (mapped : EntryFacts T.regs)
    (entry : TupleLE (pull map mapped) original)
    (fine : State Word T.regs out) (coarse : State Word S.regs out) (related : Refines map fine coarse) :
    Refines map (@SCCP.transfer _ _ _ _ model (program map p) T.bankEq mapped fine)
      (@SCCP.transfer _ _ _ _ model p S.bankEq original coarse) := by
  let fineHeader := blockFacts model (program map p).header (bankTuple fine.2.1)
  let coarseHeader := blockFacts model p.header (bankTuple coarse.2.1)
  have header : TupleLE (pull map fineHeader) coarseHeader := by
    rw [show pull map fineHeader = blockFacts model p.header (pull map (bankTuple fine.2.1)) from
      blockFacts_pull map p.header (fun q mem => safe q (by simp [Identification.quads, mem])) _]
    exact SCCP.blockFacts_mono p.header related.2
  have columns (edge : Incoming) :
      TupleLE (pull map (bankTuple (SCCP.columns model (program map p) mapped fineHeader edge)))
        (bankTuple (SCCP.columns model p original coarseHeader edge)) := by
    cases edge with
    | entry =>
      simp only [SCCP.columns, bankTuple_tupleFacts, program]
      rw [blockFacts_pull map p.preheader (fun q mem => safe q (by simp [Identification.quads, mem]))]
      exact SCCP.blockFacts_mono p.preheader entry
    | feedback side =>
      simp only [SCCP.columns, bankTuple_tupleFacts, program]
      rw [blockFacts_pull map (p.feedback side) (fun q mem => safe q (by cases side <;> simp_all [Identification.quads]))]
      exact SCCP.blockFacts_mono (p.feedback side) header
  refine ⟨?_, ?_⟩
  · apply Finset.insert_subset_insert
    change (if incomingIndex .entry ∈ fine.1 then
      SCCP.successors (fineHeader.get (map _ p.again)) (fineHeader.get (map _ p.select)) else ∅) ⊆
      (if incomingIndex .entry ∈ coarse.1 then
        SCCP.successors (coarseHeader.get p.again) (coarseHeader.get p.select) else ∅)
    by_cases marked : incomingIndex .entry ∈ fine.1
    · have again := header p.again
      have select := header p.select
      rw [pull_get] at again select
      simpa only [marked, related.1 marked, ite_true] using SCCP.successors_mono again select
    · simp only [marked, ite_false, Finset.empty_subset]
  · intro t port
    rw [pull_get]
    apply (@read_phi_le T.regs T.bankEq _ _ t _ _).mpr
    intro edge marked
    have localBound := columns edge port
    rw [pull_get] at localBound
    exact localBound.trans ((@read_phi_le S.regs S.bankEq _ _ t port _).mp le_rfl edge (related.1 marked))

theorem fifo_marks_subset (map : PortMap S T) (p : Program Op S.regs out)
    (safe : SafeWrites map p) (original : EntryFacts S.regs) (mapped : EntryFacts T.regs)
    (entry : TupleLE (pull map mapped) original) :
    (@SCCP.Worklist.solve _ _ _ _ model (program map p) T.bankEq mapped).1 ⊆
      (@SCCP.Worklist.solve _ _ _ _ model p S.bankEq original).1 := by
  rw [SCCP.Worklist.solve_eq_simultaneous, SCCP.Worklist.solve_eq_simultaneous]
  let coarse := @SCCP.solve _ _ _ _ model p S.bankEq original
  let tick := @SCCP.transfer _ _ _ _ model (program map p) T.bankEq mapped
  have invariant (steps : Nat) : Refines map (tick^[steps] ⊥) coarse := by
    induction steps with
    | zero => exact refines_bottom map coarse
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have next := transfer_refines map p safe original mapped entry (tick^[n] ⊥) coarse ih
      rw [show @SCCP.transfer _ _ _ _ model p S.bankEq original coarse = coarse from
        @SCCP.solve_fixed _ _ _ _ model p S.bankEq original] at next
      exact next
  exact (invariant (SCCP.height Word T.regs out).bound).1

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Proofs
