module

public import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Pass.Defs

/-! # Repeated checked deletion on a pure table and all its outgoing reads -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.Deletion.Iteration

open Diamond (Dataflow Model Signature Ty Val ValueSort)
open GVN (Producer)
open RVSDG (Tuple Wires extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data} {args ports : List (Ty Data)}

/-- A closed pure table with the complete ordered packet its caller reads. -/
structure Table (Op : Signature.{u, v} Data) (args ports : List (Ty Data)) where
  sigs : List (List (Ty Data))
  flow : Dataflow Op args [] sigs
  packet : Wires args (extend [] sigs) ports

def Table.eval (table : Table Op args ports) (m : Model.{u, v, w} Op) (input : Tuple (Val m.value) args) :
    Tuple (Val m.value) ports :=
  table.packet.read input (table.flow.eval m input PUnit.unit)

structure Step (table : Table Op args ports) where
  candidate : GVN.Pass.Candidate table.flow
  deleted : Deletion.Result Op args ports [] table.sigs
  accepted : delete? candidate.2 table.packet = some deleted

def Step.next {table : Table Op args ports} (step : Step table) : Table Op args ports :=
  ⟨step.deleted.erasure.sigs', step.deleted.erasure.flow, step.deleted.outputs⟩

/-- Select the first checker-accepted producer in the current numbering. -/
def first? (table : Table Op args ports) : Option (Step table) :=
  (GVN.Pass.candidates table.flow).findSome? fun candidate =>
    (delete? candidate.2 table.packet).attach.map fun deleted => ⟨candidate, deleted.1, deleted.2⟩

def NoEligible (table : Table Op args ports) : Prop :=
  ∀ {sort : ValueSort Data} (candidate : Producer table.flow sort), delete? candidate table.packet = none

/-- Positions refer to the table just before each deletion. The last table
has been scanned, including when every producer was removed. -/
inductive Trace : Table Op args ports → Table Op args ports → List Nat → Prop where
  | done (table : Table Op args ports) (stopped : first? table = none) : Trace table table []
  | step {table final : Table Op args ports} {positions : List Nat}
      (edit : Step table) (chosen : first? table = some edit) (rest : Trace edit.next final positions) :
      Trace table final (position edit.candidate.2 :: positions)

structure Result (start : Table Op args ports) where
  final : Table Op args ports
  positions : List Nat
  trace : Trace start final positions

/-- Each successful scan removes exactly one binding, leaving enough fuel
to scan the new table. A failed scan records the stopping certificate. -/
def run : (fuel : Nat) → (table : Table Op args ports) → table.sigs.length < fuel → Result table
  | 0, _, enough => (Nat.not_lt_zero _ enough).elim
  | fuel + 1, table, enough =>
    match chosen : first? table with
    | none => ⟨table, [], .done table chosen⟩
    | some edit =>
      have smaller : edit.next.sigs.length + 1 = table.sigs.length := edit.deleted.erasure.shorter
      let tail := run fuel edit.next (by omega)
      ⟨tail.final, position edit.candidate.2 :: tail.positions, .step edit chosen tail.trace⟩

def normalize (table : Table Op args ports) : Result table :=
  run (table.sigs.length + 1) table (Nat.lt_succ_self _)

end Silmaril.SSA.SeaOfNodes.Pure.Deletion.Iteration
