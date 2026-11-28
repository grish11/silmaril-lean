module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle.Thms
import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Thms
import Silmaril.SSA.Peggy.EPEG.Selection.Thms

public section

namespace Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle

open PEG
open PEG.Simple (Exec)
open RVSDG (Tuple)
open EPEG (Classes)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {source : Graph P params (result :: rest) n 1} {classes : Classes n}

/-- Each output position is paired with its own original class, even
when several positions have the same type or read a repeated vertex. -/
theorem Accepted.root_class (a : Accepted source classes) (i : Fin (result :: rest).length) :
    let p := portAt (result :: rest) i
    classes (source.roots.get p).id =
      classes (a.candidate.selection.sourceRef (a.candidate.graph.roots.get p)).id :=
  beq_iff_eq.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp a.legal.boundary).2)
    i (List.mem_finRange i))

variable {m : Interpretation.{u,v,w} P} {input : Tuple m.Value params}

/-- Includes bottom separately at every port, for every index. -/
theorem Accepted.observe_eq (a : Accepted source classes) (wf : WellFounded source.Demand)
    (valid : classes.Valid (source.denote m input wf)) (idx : Index 1) :
    source.observe m (source.denote m input wf) idx =
      a.candidate.graph.observe m (a.candidate.graph.denote m input a.reversion.demandWellFounded) idx :=
  EPEG.Selection.observe_sound_of_rows wf valid a.legal.boundary a.candidate.rows a.legal.edges idx

/-- The emitter's pass is traced back to its actual class-labelled
source representative, including when its sample is undefined. -/
theorem Accepted.pass_eq (a : Accepted source classes) (wf : WellFounded source.Demand)
    (valid : classes.Valid (source.denote m input wf)) (idx : Index 1) :
    Rules.readRef (g := a.candidate.graph)
        (a.candidate.graph.denote m input a.reversion.demandWellFounded)
        a.reversion.scalar.descriptor.pass idx =
      Rules.readRef (g := source) (source.denote m input wf)
        (a.candidate.selection.sourceRef a.reversion.scalar.descriptor.pass) idx :=
  EPEG.Selection.read_sound_of_rows _ idx wf a.reversion.demandWellFounded
    valid a.candidate.rows a.legal.edges

/-- Successful execution witnesses one first pass for all emitted slots. -/
theorem Accepted.firstExit_of_exec (a : Accepted source classes) (wf : WellFounded source.Demand)
    (valid : classes.Valid (source.denote m input wf))
    (neg : ∀ b : Bool, m.run a.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {output : Tuple m.Value (result :: rest)}
    (ran : Exec m a.output input (some output)) :
    ∃ k, Rules.readRef (g := a.candidate.graph)
        (a.candidate.graph.denote m input a.reversion.demandWellFounded)
        a.reversion.scalar.descriptor.pass idx = some ⟨k⟩ ∧
      Rules.readRef (g := source) (source.denote m input wf)
        (a.candidate.selection.sourceRef a.reversion.scalar.descriptor.pass) idx = some ⟨k⟩ ∧
      source.observe m (source.denote m input wf) idx = output.map (fun _ => some) := by
  obtain ⟨k, pass, observed⟩ := a.reversion.firstExit_of_exec neg idx ran
  exact ⟨k, pass, (a.pass_eq wf valid idx).symm.trans pass, (a.observe_eq wf valid idx).trans observed⟩

theorem Accepted.exec_iff_observe (a : Accepted source classes) (wf : WellFounded source.Demand)
    (valid : classes.Valid (source.denote m input wf)) (total : a.reversion.scalar.Total m)
    (neg : ∀ b : Bool, m.run a.reversion.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) (output : Tuple m.Value (result :: rest)) :
    Exec m a.output input (some output) ↔
      source.observe m (source.denote m input wf) idx = output.map (fun _ => some) :=
  (a.reversion.exec_iff_observe total neg idx output).trans
    (congrArg (· = output.map (fun _ => some)) (a.observe_eq wf valid idx).symm).to_iff

variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
variable {cost : Candidate source → Nat} {pool : List (Candidate source)}
variable {chosen : Accepted source classes}

theorem select_admitted (found : select classes cost pool = some chosen) :
    chosen.candidate ∈ pool ∧ check classes chosen.candidate = some chosen :=
  selectWith_admitted found

theorem select_min (found : select classes cost pool = some chosen) {other : Candidate source}
    (member : other ∈ pool) (admitted : (check classes other).isSome = true) :
    cost chosen.candidate ≤ cost other :=
  selectWith_min found member admitted

theorem select_none_iff :
    select classes cost pool = none ↔ ∀ candidate ∈ pool, check classes candidate = none :=
  selectWith_none_iff

end Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Bundle
