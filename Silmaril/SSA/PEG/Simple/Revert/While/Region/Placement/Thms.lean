module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
public import Silmaril.SSA.PEG.Figure19.Placement.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1}
variable {d : Descriptor g} {depth : Fin 1 → Nat} {branch shared : Fin n}

/-- The checked shared row has a derivation at the loop depth. Every
derivation for the same row needs at least that depth. -/
theorem BranchPlacement.placementDepth (site : BranchPlacement d depth branch shared) :
    Figure19.Derives g depth .inward (depth 0) (assumptions d (depth 0)) shared ∧
      ∀ cap ctx, Figure19.Derives g depth .inward cap ctx shared → depth 0 ≤ cap :=
  ⟨site.trueUse.derives (site.branchTyped.phiArms site.row).1,
    fun _ _ typed => site.loopUse.path.depth_le typed site.loopUse.theta⟩

/-- Partial operations on the common strict path are safe to share at
this control point whenever the update's φ is defined. -/
theorem BranchPlacement.shared_defined (site : BranchPlacement d depth branch shared)
    {m : Interpretation.{u,v,w} P} {input : Tuple m.Value carried}
    {values : g.Valuation m} {idx : Index 1} (solves : g.Solves m input values)
    (defined : (values (branch, idx)).isSome) : (values (shared, idx)).isSome :=
  site.trueUse.defined_of_phi site.row site.falseUse solves defined

/-- Accepted placement emits a SIMPLE while with a lazy branch and a
simultaneous update. The region rank is checked independently of the
typing derivation. The defined-to-successful direction uses the region's
first-pass and eval-prefix theorem under totality of both slices. -/
theorem Accepted.returns_iff_observe (accepted : Accepted g branch shared)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value carried) (total : accepted.region.Total m)
    (neg : ∀ b : Bool, m.run accepted.region.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) (value : m.Value result) :
    accepted.region.revert.Returns m input value ↔
      g.observe m (g.denote m input accepted.region.demandWellFounded) idx = .cons (some value) .nil :=
  accepted.region.returns_iff_observe m input total neg idx value

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement
