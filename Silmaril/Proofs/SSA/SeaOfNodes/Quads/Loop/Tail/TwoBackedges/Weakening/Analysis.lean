module

public import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Native
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Thms

/-! Project the original equations and least solution from the extended bank. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Proofs

open SeaOfNodes.Diamond (Model ValueSort dataPorts sortValue)
open SeaOfNodes.Diamond.SCCP (Fact gather tupleFacts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq bankTuple)
open RVSDG (Tuple)
open Join (Block)
open Semantics.Dataflow (Flat)
open Semantics.Dataflow.FiniteHeight (HeightBound)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {fresh out : ValueSort Data}
variable (m : Model.{u, v, w} Op)

theorem blockFacts_cons (block : Block Op regs) (value : Fact m.value (.value fresh))
    (bank : Tuple (Fact m.value) (dataPorts regs)) :
    SCCP.blockFacts m (block.map (quad fresh)) (.cons value bank) =
      .cons value (SCCP.blockFacts m block bank) := by
  simp only [SCCP.blockFacts_fold]
  induction block generalizing bank with
  | nil => rfl
  | cons q rest ih =>
    have step : SCCP.quadFacts m (quad fresh q) (.cons value bank) = .cons value (SCCP.quadFacts m q bank) := by
      exact congrArg (fun inputs =>
        Tuple.cons (F := Fact m.value) (t := .value fresh) value
          (write q.dest (Flat.map (m.run q.op) (gather inputs)) bank))
        (operand_reads (F := Fact m.value) (head := .value fresh) q.operands value bank)
    simp only [List.map_cons, List.foldl_cons]
    rw [step, ih]

variable (p : Program Op regs out)
variable [oldEq : BankDecidableEq m.value (dataPorts regs)]
variable (freshEq : DecidableEq (sortValue m.value fresh))
variable (input : Tuple (Fact m.value) (dataPorts regs))

theorem transfer_project (state : SCCP.State m.value (fresh :: regs) out) :
    projectState (@SCCP.transfer _ _ _ _ m (program fresh p) (extendEq freshEq oldEq) (facts fresh input) state) =
      SCCP.transfer m p input (projectState state) := by
  let oldHeader := SCCP.blockFacts m p.header (bankTuple (projectState state).2.1)
  let newerHeader :=
    SCCP.blockFacts m (program fresh p).header (bankTuple state.2.1)
  let freshFact : Fact m.value (.value fresh) := state.2.1 (0 : Fin ((dataPorts regs).length + 1))
  have header : newerHeader = .cons freshFact oldHeader :=
    blockFacts_cons m p.header _ _
  let older := SCCP.columns m p input oldHeader
  let newer := SCCP.columns m (program fresh p) (facts fresh input) newerHeader
  have columns (edge : Incoming) (i : Fin (dataPorts regs).length) :
      newer edge i.succ = older edge i := by
    cases edge with
    | entry =>
      change tupleFacts (SCCP.blockFacts m (p.preheader.map (quad fresh)) (.cons .overdefined input)) i.succ =
        tupleFacts (SCCP.blockFacts m p.preheader input) i
      rw [blockFacts_cons]
      rfl
    | feedback side =>
      change tupleFacts (SCCP.blockFacts m ((p.feedback side).map (quad fresh)) newerHeader) i.succ =
        tupleFacts (SCCP.blockFacts m (p.feedback side) oldHeader) i
      rw [header, blockFacts_cons m (p.feedback side) freshFact oldHeader]
      rfl
  have phi : (fun (i : Fin (dataPorts regs).length) => (@SCCP.phiFacts _ _ _ (extendEq freshEq oldEq) state.1 newer) i.succ) =
      SCCP.phiFacts state.1 older := by
    funext i
    unfold SCCP.phiFacts
    change (letI := oldEq.atPort i
      (SCCP.gate state.1 (SCCP.incomingIndex .entry) (newer .entry i.succ) ⊔
        SCCP.gate state.1 (SCCP.incomingIndex (.feedback true)) (newer (.feedback true) i.succ)) ⊔
          SCCP.gate state.1 (SCCP.incomingIndex (.feedback false)) (newer (.feedback false) i.succ)) = _
    rw [columns, columns, columns]
  change (insert (SCCP.incomingIndex .entry) (if SCCP.incomingIndex .entry ∈ state.1 then
      SCCP.successors (newerHeader.get (.tail p.again)) (newerHeader.get (.tail p.select)) else ∅),
    (fun (i : Fin (dataPorts regs).length) => (@SCCP.phiFacts _ _ _ (extendEq freshEq oldEq) state.1 newer) i.succ),
    SCCP.gate state.1 SCCP.exitIndex (newerHeader.get (.tail p.result))) = _
  rw [phi, header]
  rfl

private def extendState {value : Data → Type w} (state : SCCP.State value regs out) :
    SCCP.State value (fresh :: regs) out :=
  (state.1, fun i => Fin.cases (motive := fun j => Fact value (dataPorts (fresh :: regs))[j])
    .overdefined state.2.1 i, state.2.2)

private theorem le_extend_iff {value : Data → Type w} (newer : SCCP.State value (fresh :: regs) out)
    (older : SCCP.State value regs out) :
    newer ≤ extendState older ↔ projectState newer ≤ older := by
  constructor
  · exact fun h => ⟨h.1, (fun i => h.2.1 i.succ), h.2.2⟩
  · intro h
    refine ⟨h.1, (fun i => ?_), h.2.2⟩
    exact Fin.cases (le_top : newer.2.1 (0 : Fin ((dataPorts regs).length + 1)) ≤ ⊤) (fun j => h.2.1 j) i

theorem solve_project :
    projectState (@SCCP.solve _ _ _ _ m (program fresh p) (extendEq freshEq oldEq) (facts fresh input)) =
      SCCP.solve m p input := by
  let original := SCCP.solve m p input
  let widened := @SCCP.solve _ _ _ _ m (program fresh p) (extendEq freshEq oldEq) (facts fresh input)
  have fixed : SCCP.transfer m p input (projectState widened) = projectState widened := by
    rw [← transfer_project m p freshEq, SCCP.solve_fixed]
  have prefixed : @SCCP.transfer _ _ _ _ m (program fresh p) (extendEq freshEq oldEq)
      (facts fresh input) (extendState original) ≤ extendState original := by
    apply (le_extend_iff _ _).2
    rw [transfer_project]
    exact le_of_eq (SCCP.solve_fixed m p input)
  have bound : widened ≤ extendState original :=
    (SCCP.height m.value (fresh :: regs) out).solve_le_of_prefixed
      (@SCCP.transferHom _ _ _ _ m (program fresh p) (extendEq freshEq oldEq) (facts fresh input)) prefixed
  exact le_antisymm ((le_extend_iff _ _).1 bound) ((SCCP.solve_isLeast m p input).2 fixed)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Weakening.Proofs
