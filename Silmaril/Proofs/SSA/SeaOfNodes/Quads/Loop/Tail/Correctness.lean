module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Proofs

open Diamond (Model Ty ValueSort dataPorts sortValue)
open RVSDG (Wires)
open Join (Block)
open Blocks (Bank)
open SeaOfNodes.Loop (Graph Incoming)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

theorem runFrom_mono {n : Nat} {source : Source Op regs out n} (m : Model.{u, v, w} Op)
    {fuel larger : Nat} {id : Fin n} {bank : Bank (regs := regs) m} {value : sortValue m.value out}
    (enough : fuel ≤ larger) (returned : source.runFrom m fuel id bank = some value) :
    source.runFrom m larger id bank = some value := by
  induction fuel generalizing larger id bank with
  | zero => cases returned
  | succ fuel ih =>
    cases larger with
    | zero => omega
    | succ larger =>
      simp only [Source.runFrom] at returned ⊢
      cases edge : (source id).terminator.select m ((source id).body.eval m bank) with
      | jump target =>
        rw [edge] at returned
        exact ih (Nat.le_of_succ_le_succ enough) returned
      | ret port =>
        rw [edge] at returned
        exact returned

variable {src : Source Op regs out} {p : Program Op regs out}

theorem source_of_check (accepted : src.check = some p) : p.source = src := by
  unfold Source.check at accepted
  split at accepted
  next toHeader toLatch test feedback result hentry hheader hlatch =>
    split at accepted
    next shape =>
      rcases shape with ⟨rfl, rfl, rfl⟩
      cases accepted
      funext i
      have bound := i.isLt
      have places : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases places with rfl | rfl | rfl
      · cases hh : src 0
        simp_all [Program.source]
      · cases hh : src 1
        simp_all [Program.source]
      · cases hh : src 2
        simp_all [Program.source]
    next => contradiction
  next => contradiction

theorem append_outgoing {args : List (Ty Data)} {past : List (List (Ty Data))}
    (first second : Block Op regs) (current : Wires args past (dataPorts regs)) :
    HEq (CFG.compileBlock (first ++ second) current).outgoing
      (CFG.compileBlock second (CFG.compileBlock first current).outgoing).outgoing := by
  induction first generalizing past with
  | nil => rfl
  | cons quad rest ih => exact ih (rebind current quad.dest)

variable (p : Program Op regs out) (m : Model.{u, v, w} Op)
variable (input old : Bank (regs := regs) m)

theorem feedback_column : p.lower.phiInputs .backedge = p.feedbackColumn := by
  have fused := append_outgoing p.header p.latch.body (headerVersions regs)
  have transport : HEq p.feedbackColumn p.latchTransfer.outgoing := by
    unfold Program.feedbackColumn
    exact cast_heq _ _
  exact eq_of_heq (fused.trans transport.symm)

theorem latch_agrees (edge : Incoming) :
    p.fuse.latch m edge input old =
      edge.select (p.entry.eval m input) (p.latch.body.eval m (p.header.eval m old)) := by
  rw [p.fuse.latch_agrees]
  cases edge with
  | entry => rfl
  | backedge => exact List.foldl_append

private theorem run_header (fuel : Nat) :
    p.source.runFrom m (fuel + 2) 1 old =
      match p.fuse.step m old with
      | .inl result => some result
      | .inr next => p.source.runFrom m fuel 1 next := by
  simp only [Source.runFrom, Program.source, Fin.reduceEq, ↓reduceIte, Terminator.select,
    Blocks.Program.step, Program.fuse, Block.eval, List.foldl_append]
  by_cases taken : ((p.latch.body.eval m (p.header.eval m old)).get p.latch.test).down = true
  all_goals
    simp only [Block.eval] at taken
    simp [taken]

private theorem run_header_budget : (fuel : Nat) → (old : Bank (regs := regs) m) →
    p.source.runFrom m (fuel + 2) 1 old = p.fuse.evalFrom m (fuel / 2) old
  | 0, old => by
    rw [run_header, Blocks.Program.evalFrom]
    cases p.fuse.step m old <;> rfl
  | 1, old => by
    rw [run_header, Blocks.Program.evalFrom]
    cases p.fuse.step m old <;> rfl
  | fuel + 2, old => by
    rw [run_header, show (fuel + 2) / 2 = fuel / 2 + 1 by omega, Blocks.Program.evalFrom]
    cases p.fuse.step m old with
    | inl _ => rfl
    | inr next => exact run_header_budget fuel next

theorem lower_run : (fuel : Nat) → p.source.run m fuel input =
    if 3 ≤ fuel then p.lower.evalBackedges m ((fuel - 3) / 2) input else none
  | 0 | 1 | 2 => rfl
  | fuel + 3 => by
    rw [ite_eq_left (by omega), show fuel + 3 - 3 = fuel by omega]
    exact (run_header_budget p m fuel (p.entry.eval m input)).trans
      (p.fuse.lower_evalBackedges m input (fuel / 2)).symm

theorem returns_iff (accepted : src.check = some p) (result : sortValue m.value out) :
    p.lower.Returns m input result ↔ ∃ fuel, src.run m fuel input = some result := by
  rw [← source_of_check accepted, Graph.returns_iff_evalBackedges]
  constructor
  · rintro ⟨budget, run⟩
    refine ⟨2 * budget + 3, ?_⟩
    rw [lower_run, ite_eq_left (by omega), show (2 * budget + 3 - 3) / 2 = budget by omega]
    exact run
  · rintro ⟨fuel, run⟩
    rw [lower_run] at run
    split at run
    · exact ⟨_, run⟩
    · contradiction

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Proofs
