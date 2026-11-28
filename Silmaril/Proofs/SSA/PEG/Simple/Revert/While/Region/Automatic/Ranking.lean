module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Thms
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Proofs

open Silmaril.Isotope.LambdaSSA.Acyclic.Positional

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable (g : Graph P carried [result] n 1)

private theorem phaseEdge {a b : Fin n} {kind : EdgeKind (Fin 1)} {height : Fin n → Nat}
    (lt : height b < height a) :
    DemandRank.checkEdge [.phase height] a b kind = true := by
  simp [DemandRank.checkEdge, RankComponent.change, lt]

private theorem lt_of_phaseEdge {a b : Fin n} {kind : EdgeKind (Fin 1)}
    {height : Fin n → Nat} (ok : DemandRank.checkEdge [.phase height] a b kind = true) :
    height b < height a := by
  by_contra nf
  by_cases eq : height b = height a <;>
    simp [DemandRank.checkEdge, RankComponent.change, nf, eq] at ok

private theorem local_mem (i : Fin n) (slot : Fin (g.node i).inputs.length)
    (ph : (RankComponent.phase (phase g)).change i ((g.node i).arg slot).id
      ((g.node i).label.kind slot) = .equal)
    (co : (RankComponent.counter 0).change i ((g.node i).arg slot).id
      ((g.node i).label.kind slot) = .equal) :
    ((g.node i).arg slot).id ∈ localTargets g i := by
  apply List.mem_filterMap.mpr
  exact ⟨slot, List.mem_finRange slot, by simp [ph, co]⟩

theorem rank_accepts (height : Fin n → Nat) (bounded : ∀ i, height i < n)
    (ok : DemandRank.check [.phase (phase g), .counter 0, .phase height] g = true) :
    (inferDemandRank g).check g = true := by
  have rankAt (i : Fin n) (s : Fin (g.node i).inputs.length) :=
    List.all_eq_true.mp (List.all_eq_true.mp ok i (List.mem_finRange i)) s (List.mem_finRange s)
  have complete : Rank.check (localTargets g) = true := by
    apply Rank.check_complete _ height _ bounded
    intro i j edge
    obtain ⟨s, _, picked⟩ := List.mem_filterMap.mp edge
    dsimp only at picked
    split at picked
    next equal =>
      obtain ⟨ph, co⟩ := equal
      obtain rfl := Option.some.inj picked
      have valid := rankAt i s
      simp only [DemandRank.checkEdge, ph, co] at valid
      exact lt_of_phaseEdge valid
    next => cases picked
  apply List.all_eq_true.mpr
  intro i _
  apply List.all_eq_true.mpr
  intro s _
  let j := ((g.node i).arg s).id
  let kind := (g.node i).label.kind s
  have old := rankAt i s
  change DemandRank.checkEdge [.phase (phase g), .counter 0, .phase height] i j kind = true at old
  change DemandRank.checkEdge (inferDemandRank g) i j kind = true
  cases ph : (RankComponent.phase (phase g)).change i j kind with
  | lower => simp [inferDemandRank, DemandRank.checkEdge, ph]
  | unknown => simp [DemandRank.checkEdge, ph] at old
  | equal =>
    cases co : (RankComponent.counter 0).change i j kind with
    | lower => simp [inferDemandRank, DemandRank.checkEdge, ph, co]
    | unknown => simp [DemandRank.checkEdge, ph, co] at old
    | equal =>
      have edge := local_mem g i s ph co
      have decreases := Rank.check_sound _ complete edge
      simp only [inferDemandRank, DemandRank.checkEdge, ph, co]
      exact phaseEdge decreases

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Proofs
