module

public import Silmaril.SSA.PEG.Figure19.Placement.MustEval.Defs
public import Silmaril.SSA.PEG.Figure19.Placement.Thms

public section

namespace Silmaril.SSA.PEG.Figure19.MustEval.Proofs

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {i target : Fin n}
variable {m : Interpretation.{u,v,w} P} {env : RVSDG.Tuple m.Value params}
variable {values : g.Valuation m} {idx : Index l}

theorem sound (solves : g.Solves m env values) (fuel : Nat)
    (hit : target ∈ (rounds g fuel)[i.val]) (root : (values (i, idx)).isSome) :
    (values (target, idx)).isSome := by
  induction fuel generalizing i with
  | zero =>
    simp only [rounds, Vector.getElem_ofFn, Fin.eta, Finset.mem_singleton] at hit
    exact hit.symm ▸ root
  | succ k ih =>
    simp only [rounds, Vector.getElem_ofFn, Fin.eta, transfer, Finset.mem_insert] at hit
    rcases hit with rfl | hit
    · exact root
    split at hit
    · rename_i ins instr args row
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hit
      obtain ⟨slot, demanded⟩ := hit
      exact ih demanded ((StrictPath.operand args row slot .here).defined solves root)
    · rename_i row
      rw [Finset.mem_union, Finset.mem_inter] at hit
      obtain ⟨cond, arm⟩ := phi_demands row solves root
      rcases hit with hit | ⟨yesHit, noHit⟩
      · exact ih hit cond
      · exact arm.elim (ih yesHit) (ih noHit)
    · exact False.elim (Finset.notMem_empty _ hit)

private theorem round_read (g : Graph P params results n l) (k : Nat) (i : Fin n) :
    (rounds g (k + 1))[i.val] = transfer g (rounds g k) i := by
  simp only [rounds, Vector.getElem_ofFn, Fin.eta]

theorem stable {rank : Fin n → Nat} (ranked : Ranked g rank) (fuel : Nat)
    (within : rank i < fuel) : (rounds g (fuel + 1))[i.val] = (rounds g fuel)[i.val] := by
  induction fuel generalizing i with
  | zero => exact (Nat.not_lt_zero _ within).elim
  | succ k ih =>
    rw [round_read, round_read]
    unfold transfer
    congr 1
    have children := ranked i
    split
    · rename_i ins instr args row
      rw [row] at children
      unfold Decreases at children
      congr 1
      funext slot
      have lt : rank (args.get (portAt ins slot)).id < rank i := children rfl slot
      exact ih (by omega)
    · rename_i args row
      rw [row] at children
      unfold Decreases at children
      have less (slot : Fin 3) : rank (args.get (portAt [.bool, g.sort i, g.sort i] slot)).id < k :=
        Nat.lt_of_lt_of_le (children rfl slot) (Nat.le_of_lt_succ within)
      have cond := ih (less 0)
      have yes := ih (less 1)
      have no := ih (less 2)
      change (rounds g (k + 1))[(args.get .head).id.val] =
        (rounds g k)[(args.get .head).id.val] at cond
      change (rounds g (k + 1))[(args.get (.tail .head)).id.val] =
        (rounds g k)[(args.get (.tail .head)).id.val] at yes
      change (rounds g (k + 1))[(args.get (.tail (.tail .head))).id.val] =
        (rounds g k)[(args.get (.tail (.tail .head))).id.val] at no
      rw [cond, yes, no]
    · rfl

end Silmaril.SSA.PEG.Figure19.MustEval.Proofs
