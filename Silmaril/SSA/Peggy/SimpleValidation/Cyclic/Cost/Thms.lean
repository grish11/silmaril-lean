module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Defs
public import Silmaril.SSA.Peggy.EPEG.Selection.Legality.Thms
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
import Silmaril.SSA.Peggy.EPEG.Selection.Thms
import Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.Selection

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost

open PEG
open EPEG (Classes)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {source : Graph P params [result] n 1} {classes : Classes n}

theorem Legal.feedbackCycles {candidate : Candidate source} (legal : Legal classes candidate) :
    candidate.graph.FeedbackCycles :=
  legal.feedback.feedbackCycles

variable {m : Interpretation.{u,v,w} P} {input : Tuple m.Value params}

/-- Class validity is a semantic contract on the source partition. The
checked extraction preserves the ordered option-valued result at every index. -/
theorem Accepted.observe_eq (a : Accepted source classes) (wf : WellFounded source.Demand)
    (valid : classes.Valid (source.denote m input wf)) (i : Index 1) :
    source.observe m (source.denote m input wf) i =
      a.candidate.graph.observe m (a.candidate.graph.denote m input a.reversion.demandWellFounded) i :=
  EPEG.Selection.observe_sound_of_rows wf valid a.legal.boundary a.candidate.rows a.legal.edges i

/-- The emitted program's finite returns are sound even for partial primitives. -/
theorem Accepted.observe_of_returns (a : Accepted source classes) (wf : WellFounded source.Demand)
    (valid : classes.Valid (source.denote m input wf))
    (neg : ∀ b : Bool, m.run a.reversion.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index 1) {value : m.Value result} (ran : a.output.Returns m input value) :
    source.observe m (source.denote m input wf) i = .cons (some value) .nil :=
  (a.observe_eq wf valid i).trans (a.reversion.observe_of_returns m input neg i ran)

/-- The converse also needs total guard and full-update slices on defined stores. -/
theorem Accepted.returns_iff_observe (a : Accepted source classes) (wf : WellFounded source.Demand)
    (valid : classes.Valid (source.denote m input wf)) (total : a.reversion.Total m)
    (neg : ∀ b : Bool, m.run a.reversion.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i : Index 1) (value : m.Value result) :
    a.output.Returns m input value ↔
      source.observe m (source.denote m input wf) i = .cons (some value) .nil :=
  (a.reversion.returns_iff_observe m input total neg i value).trans
    (congrArg (· = .cons (some value) .nil) (a.observe_eq wf valid i).symm).to_iff

section Checked

variable {results : List (Ty Data)} {g : Graph P params results n 1}
variable {Certificate : Candidate g → Type w} {emit : ∀ c, Option (Certificate c)}
variable {cost : Candidate g → Nat} {pool : List (Candidate g)}
variable {chosen : Checked g classes Certificate}

theorem selectWith_admitted (found : selectWith classes emit cost pool = some chosen) :
    chosen.candidate ∈ pool ∧ chosen.candidate.checkWith classes emit = some chosen :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.selected found

theorem selectWith_min (found : selectWith classes emit cost pool = some chosen) {other : Candidate g}
    (member : other ∈ pool) (admitted : (other.checkWith classes emit).isSome = true) :
    cost chosen.candidate ≤ cost other :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.minimal found member admitted

theorem selectWith_none_iff :
    selectWith classes emit cost pool = none ↔ ∀ candidate ∈ pool, candidate.checkWith classes emit = none :=
  Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost.select_none

end Checked

variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
variable {cost : Candidate source → Nat} {pool : List (Candidate source)}
variable {chosen : Accepted source classes}

theorem select_admitted (found : select classes cost pool = some chosen) :
    chosen.candidate ∈ pool ∧ chosen.candidate.check classes = some chosen :=
  selectWith_admitted found

theorem select_min (found : select classes cost pool = some chosen) {other : Candidate source}
    (member : other ∈ pool) (admitted : (other.check classes).isSome = true) :
    cost chosen.candidate ≤ cost other :=
  selectWith_min found member admitted

theorem select_none_iff :
    select classes cost pool = none ↔ ∀ candidate ∈ pool, candidate.check classes = none :=
  selectWith_none_iff

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost
