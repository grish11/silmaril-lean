module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Automatic.Ranking
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Automatic.Recognition

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1}

/-- Inference succeeds at the demand-rank gate whenever the fixed
eval/pass phases and the loop counter admit a bounded final component. -/
theorem inferDemandRank_check (height : Fin n → Nat) (bounded : ∀ i, height i < n)
    (valid : DemandRank.check [.phase (phase g), .counter 0, .phase height] g = true) :
    (inferDemandRank g).check g = true :=
  Proofs.rank_accepts g height bounded valid

/-- Recover a wired boundary when the θ table has one candidate for each
initializer port and no extra θ rows. -/
theorem inferBoundary_eq [DecidableEq Data] (d : Descriptor g) (b : Boundary g d)
    (count : thetaCount g = carried.length)
    (unique : ∀ t (p : Port carried t) i, i ≠ (d.theta.get p).id → candidate g p i = none) :
    inferBoundary g = some d :=
  Proofs.boundary_eq d b count unique

/-- Relative completeness for boundaries already schedulable by the
region checker, with unique θ initializers and a bounded rank in the
eval/pass phase layout. The witnesses are used only in this theorem. -/
theorem extract_accepts [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (d : Descriptor g) (b : Boundary g d) (count : thetaCount g = carried.length)
    (unique : ∀ t (p : Port carried t) i, i ≠ (d.theta.get p).id → candidate g p i = none)
    (height : Fin n → Nat) (bounded : ∀ i, height i < n)
    (valid : DemandRank.check [.phase (phase g), .counter 0, .phase height] g = true)
    (scheduled : (checkScheduled g d [.phase (phase g), .counter 0, .phase height]).isSome = true) :
    (extract g).isSome = true := by
  unfold extract
  rw [inferBoundary_eq d b count unique]
  exact (Proofs.checkScheduled_isSome_rank d (inferDemandRank_check height bounded valid) valid).trans
    scheduled

/-- The certificate returned by inference gives the exact defined-return
correspondence of the region checker under its guard, full-update and
negation premises. -/
theorem extract_returns_iff_observe [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (accepted : (extract g).isSome) (m : Interpretation.{u,v,w} P)
    (input : Tuple m.Value carried) (idx : Index 1) (value : m.Value result) :
    let cert := (extract g).get accepted
    cert.Total m →
    (∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩) →
    (cert.revert.Returns m input value ↔
      g.observe m (g.denote m input cert.demandWellFounded) idx = .cons (some value) .nil) :=
  fun total neg => ((extract g).get accepted).returns_iff_observe m input total neg idx value

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic
