module

public import Silmaril.SSA.PEG.Figure19.Defs

public section

namespace Silmaril.SSA.PEG.Figure19.Proofs

open RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {depth : Fin l → Nat}
variable {direction : EvalDirection} {cap : Nat} {ctx : Assumptions n} {i : Fin n}

theorem evalBoundary (h : Derives g depth direction cap ctx i) :
    EvalBoundary g depth direction cap i := by
  induction h with
  | param row | op row _ _ | phi row _ _ _ _ _ _ | theta row _ _ _ _ _ | assume row _ =>
    simp [EvalBoundary, row, Node.ofLabel]
  | evalPass row pass step _ _ _ _ _ =>
    simp only [EvalBoundary, row, Node.ofLabel]
    exact ⟨_, Nat.le_refl _, step, _, pass⟩
  | reduce le _ _ ih =>
    unfold EvalBoundary at *
    split <;> try trivial
    rename_i row
    rw [row] at ih
    obtain ⟨host, bound, arrow, test⟩ := ih
    exact ⟨host, Nat.le_trans bound le, arrow, test⟩

theorem printed_no_root_eval (h : CFGContext g depth .printed) (slot : Fin results.length)
    {key : Fin l} {args : Tuple (Ref g.sort) [g.sort (g.roots.get (portAt results slot)).id, .count]}
    (row : g.node (g.roots.get (portAt results slot)).id = .ofLabel (.eval key) args) : False := by
  have boundary := evalBoundary (h slot)
  simp only [EvalBoundary, row, Node.ofLabel, EvalDirection.Allows] at boundary
  obtain ⟨host, bound, direction, _⟩ := boundary
  omega

end Silmaril.SSA.PEG.Figure19.Proofs
