module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Unrolled.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.BitLoop.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Reduction

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.Extension.Singleton.Rounds
open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false

variable {p q : Program} {a b : Poll} {m n : Nat}

theorem unrolled_loop (p : Program) (law : Unrolls N n) :
    WithGuardedTablePacking.Eqv false [State] (unrolled p n) (loopRegion p) [Bit] :=
  unrolled_eqv N law (step_typed p)

theorem unrolled_iff_loops (lm : Unrolls N m) (ln : Unrolls N n) :
    WithGuardedTablePacking.Eqv false [State] (unrolled p m) (unrolled q n) [Bit] ↔
      WithGuardedTablePacking.Eqv false [State] (loopRegion p) (loopRegion q) [Bit] :=
  ⟨fun h => (unrolled_loop p lm).symm.trans (h.trans (unrolled_loop q ln)),
    fun h => (unrolled_loop p lm).trans (h.trans (unrolled_loop q ln).symm)⟩

theorem unrolled_valid_iff_loops (lm : Unrolls N m) (ln : Unrolls N n) :
    Valid (unrolled_typed p m).hasType (unrolled_typed q n).hasType ↔
      Valid (loop_typed p).hasType (loop_typed q).hasType := by
  have left : Valid (unrolled_typed p m).hasType (loop_typed p).hasType :=
    valid_of_eqv false (unrolled_loop p lm) _ _
  have right : Valid (unrolled_typed q n).hasType (loop_typed q).hasType :=
    valid_of_eqv false (unrolled_loop q ln) _ _
  exact ⟨fun h => Valid.trans (Valid.symm left) (Valid.trans h right),
    fun h => Valid.trans left (Valid.trans h (Valid.symm right))⟩

theorem unrolled_packed (p : Program) (n : Nat) :
    ∃ (R : Fin 1 → Ty Empty) (e : Region signature.Instr) (blocks : Fin 1 → Region signature.Instr)
      (he : ValueBranches [State] e (List.ofFn R ++ [Bit]))
      (hb : ∀ i, ValueBranches [R i, State] (blocks i) (List.ofFn R ++ [Bit])),
      unrolled p n = .cfg e 1 blocks ∧
        WithGuardedTablePacking.Eqv false [State] (unrolled p n) (packedReadbackRep R he hb).val [Bit] := by
  obtain ⟨e, blocks, table⟩ : ∃ e blocks, unrolled p n = Region.cfg e 1 blocks := ⟨_, _, rfl⟩
  have typed := unrolled_typed p n
  rw [table] at typed
  cases typed with
  | cfg R he hb =>
    refine ⟨R, e, blocks, he, hb, table, ?_⟩
    rw [table]
    exact WithGuardedTablePacking.pack false R he hb

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop
