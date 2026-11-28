module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Thms
public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Proofs

open SeaOfNodes.Diamond (Model Val ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open Tail.Diamond.MLIR.CF.Pruned.Reindex (Permutation pull pull_get)
open RVSDG (Port Tuple)
open Blocks (Bank)
open Join (Block)

universe u v w

theorem tuple_ext {T : Type u} {F : T → Type w} {ports : List T} {a b : Tuple F ports}
    (h : ∀ {t} (p : Port ports t), a.get p = b.get p) : a = b := by
  rw [← tabulate_get_eq a, ← tabulate_get_eq b]
  exact congrArg (tabulate ports) (funext (fun _ => funext h))

theorem slot_eq {T : Type u} {ports : List T} {s t : T}
    (p : Port ports s) (q : Port ports t) (h : slot p = slot q) :
    (⟨s, p⟩ : Sigma (Port ports)) = ⟨t, q⟩ := by
  induction p with
  | head => cases q <;> simp_all [slot]
  | tail p ih =>
    cases q with
    | head => simp [slot] at h
    | tail q =>
      exact congrArg (fun a => Sigma.mk a.1 (Port.tail a.2)) (ih q (Nat.succ.inj h))

theorem pull_write {T : Type u} {F : T → Type w} {old new : List T} {t : T}
    (order : Permutation old new) (dest : Port old t) (value : F t) (bank : Tuple F new) :
    pull order (write (order t dest) value bank) = write dest value (pull order bank) := by
  apply tuple_ext
  intro s p
  by_cases eq : slot p = slot dest
  · obtain ⟨rfl, hp⟩ := Sigma.mk.inj_iff.mp (slot_eq p dest eq)
    obtain rfl := eq_of_heq hp
    rw [pull_get, get_write_same, get_write_same]
  · have ne : slot (order s p) ≠ slot (order t dest) := by
      intro h
      apply eq
      exact congrArg (fun a : Sigma (Port old) => slot a.2)
        (show (⟨s, p⟩ : Sigma (Port old)) = ⟨t, dest⟩ by
          simpa using congrArg (fun a : Sigma (Port new) => (⟨a.1, (order a.1).symm a.2⟩ : Sigma (Port old)))
            (slot_eq (order s p) (order t dest) h))
    rw [pull_get, get_write_other _ _ _ _ ne, get_write_other _ _ _ _ eq, pull_get]

theorem read_renamed {T : Type u} {F : T → Type w} {old new ports : List T}
    (order : Permutation old new) (operands : Tuple (Port old) ports) (bank : Tuple F new) :
    (operands.map (fun t => order t)).map (fun _ p => bank.get p) =
      operands.map (fun _ p => (pull order bank).get p) := by
  induction operands with
  | nil => rfl
  | cons p _ ih => simp only [Tuple.map, pull_get, ih]

theorem covers_iff {Data : Type u} {value : Data → Type w}
    {old new : List (ValueSort Data)} (order : Registers old new)
    (facts : Tuple (Fact value) (dataPorts old)) (input : Tuple (Val value) (dataPorts new)) :
    TupleCovers (push order facts) input ↔ TupleCovers facts (pull order input) := by
  constructor
  · intro covered t p
    simpa [push, pull_get, Permutation.symm] using covered (order t p)
  · intro covered t p
    simpa [push, pull_get, Permutation.symm] using covered ((order t).symm p)

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {old new : List (ValueSort Data)} {out : ValueSort Data}
variable (order : Registers old new) (m : Model.{u, v, w} Op)

theorem block_eval (block : Block Op old) (input : Bank (regs := new) m) :
    pull order (Block.eval (block.map (quad order)) m input) = block.eval m (pull order input) := by
  induction block generalizing input with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.map_cons, Block.eval, List.foldl_cons] at *
    rw [ih]
    apply congrArg (fun bank => Block.eval rest m bank)
    simp only [Quad.eval, quad, read_renamed]
    exact pull_write (F := Val m.value) order q.dest _ input

private theorem step_eq (p : Program Op old out) (bank : Bank (regs := new) m) :
    (match (program order p).step m bank with
    | .inl value => Sum.inl value
    | .inr (side, next) => .inr (side, pull order next)) =
      p.step m (pull order bank) := by
  let current := Block.eval (p.header.map (quad order)) m bank
  have reads := block_eval order m p.header bank
  change pull order current = _ at reads
  simp only [Program.step, program]
  change (match (if (current.get (order _ p.again)).down then
    Sum.inr ((current.get (order _ p.select)).down,
      Block.eval ((p.feedback (current.get (order _ p.select)).down).map (quad order)) m current)
    else Sum.inl (current.get (order _ p.result))) with
    | .inl value => Sum.inl value
    | .inr (side, next) => .inr (side, pull order next)) = _
  rw [← reads]
  simp only [pull_get]
  cases (current.get (order _ p.again)).down <;> simp [block_eval] <;> rfl

private theorem header_run (p : Program Op old out) (fuel : Nat) (input : Bank (regs := new) m) :
    (program order p).source.runFrom m fuel 1 input = p.source.runFrom m fuel 1 (pull order input) := by
  induction fuel using Nat.strong_induction_on generalizing input with
  | ind fuel ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      rw [Program.source_header, Program.source_header, ← step_eq order m]
      cases (program order p).step m input with
      | inl _ => rfl
      | inr edge =>
        obtain ⟨side, bank⟩ := edge
        exact ih (fuel - 2) (by omega) bank

theorem source_run (p : Program Op old out) (fuel : Nat) (input : Bank (regs := new) m) :
    (program order p).source.runFrom m fuel 0 input = p.source.runFrom m fuel 0 (pull order input) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [Program.source_entry, Program.source_entry, header_run]
    change p.source.runFrom m fuel 1 (pull order (Block.eval (p.preheader.map (quad order)) m input)) = _
    rw [block_eval]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Reindex.Proofs
