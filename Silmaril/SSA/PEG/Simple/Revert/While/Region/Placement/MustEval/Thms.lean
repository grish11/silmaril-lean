module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.MustEval.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.Thms
public import Silmaril.SSA.PEG.Figure19.Placement.MustEval.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.MustEval

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1}
variable {d : Descriptor g} {depth : Fin 1 → Nat}

/-- A proposed shared computation is already defined wherever the
feedback branch is defined, on that same old state. -/
theorem Candidate.shared_defined (site : Candidate d depth (Figure19.MustEval.analyze g))
    {m : Interpretation.{u,v,w} P} {input : Tuple m.Value carried}
    {values : g.Valuation m} {idx : Index 1} (solves : g.Solves m input values)
    (defined : (values (site.branch, idx)).isSome) : (values (site.shared, idx)).isSome :=
  (Figure19.phi_demands site.row solves defined).2.elim
    (Figure19.MustEval.defined solves n site.trueUse)
    (Figure19.MustEval.defined solves n site.falseUse)

theorem Accepted.observe_of_returns (a : Accepted g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value carried)
    (neg : ∀ b : Bool, m.run a.region.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {value : m.Value result} (ran : a.region.revert.Returns m input value) :
    g.observe m (g.denote m input a.region.demandWellFounded) idx = .cons (some value) .nil :=
  a.region.observe_of_returns m input neg idx ran

/-- The converse uses totality of the whole guard and lazy update slice
because the designated PEG result can discard other carried slots. -/
theorem Accepted.returns_iff_observe (a : Accepted g)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value carried) (total : a.region.Total m)
    (neg : ∀ b : Bool, m.run a.region.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) (value : m.Value result) :
    a.region.revert.Returns m input value ↔
      g.observe m (g.denote m input a.region.demandWellFounded) idx = .cons (some value) .nil :=
  a.region.returns_iff_observe m input total neg idx value

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Placement.MustEval
