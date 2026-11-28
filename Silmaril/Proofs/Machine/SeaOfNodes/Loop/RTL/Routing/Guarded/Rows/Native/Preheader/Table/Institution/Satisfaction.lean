module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Defs
public import Silmaril.Logic.Institution.Observational.Sentence

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv instruction)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber (inputModel)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes
open Silmaril.Isotope.Institution.Observational (ret_mem_ssaBeh scoped_eval_congr)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound_agrees)
open Silmaril.Logic.Institution.Observational (Sentence)

variable {arity : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}
variable {left : SourceWithEntry arity entrySigs sigs} {right : SourceWithEntry arity rightEntry rightSigs}
variable {leftTargets rightTargets : Checked.Phi.Targets}

theorem lambdaReturns_eq (input : WordTuple arity) (initial : Memory) (region : LambdaScope arity) :
    lambdaReturns input initial region = Rows.lambdaObservation region.val input initial := by
  ext ⟨value, final⟩
  let M := inputModel (P := Rows.wordSignature) model Memory input
  exact ret_mem_ssaBeh.trans (scoped_eval_congr region.property (envOfBound_agrees M.bound) (fun _ => rfl))

theorem observations_eq (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    Rows.rtlObservation leftTargets.1 input initial = {result | result ∈ nativeDenote left input initial} ∧
      lambdaReturns input initial (scope accepted) = {result | result ∈ nativeDenote left input initial} := by
  obtain ⟨rtl, typed⟩ := denotations_eq accepted input initial
  constructor
  · ext ⟨value, final⟩
    change leftTargets.1.oracle 0 (words input) initial [value] final ↔ (value, final) ∈ nativeDenote left input initial
    simpa only [rtl] using (mem_rtlDenote_iff leftTargets.1 input initial final value).symm
  · rw [lambdaReturns_eq]
    ext ⟨value, final⟩
    change Eval (instruction model) (inputEnv model input) leftTargets.2 initial 0
      (Generic.packResult model (out := word) value) final ↔ (value, final) ∈ nativeDenote left input initial
    simpa only [typed] using (mem_lambdaDenote_iff leftTargets.2 input initial final value).symm

private theorem returnSets_eq_iff (lhs rhs : Part Word) (initial : Memory) :
    { result : Word × Memory | result ∈ lhs.map (fun value => (value, initial)) } =
      { result : Word × Memory | result ∈ rhs.map (fun value => (value, initial)) } ↔ lhs = rhs := by
  let attach : Word → Word × Memory := fun value => (value, initial)
  constructor
  · intro same
    have mapped : lhs.map attach = rhs.map attach := Part.ext fun result =>
      Iff.of_eq (congrArg (fun s : Set (Word × Memory) => result ∈ s) same)
    have projected := congrArg (Part.map Prod.fst) mapped
    have cancels (p : Part Word) : Part.map Prod.fst (p.map attach) = p := by
      rw [Part.map_map]
      exact Part.map_id' (fun _ => rfl) p
    exact (cancels lhs).symm.trans (projected.trans (cancels rhs))
  · rintro rfl
    rfl

theorem equation_at_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets)
    (input : WordTuple arity) (initial : Memory) :
    let native := left.denote model input = right.denote model input
    ((Sentence.eq leftTargets.1 rightTargets.1).Holds (fun target => Rows.rtlObservation target input initial)
        ↔ native) ∧
      ((Sentence.eq (scope leftChecked) (scope rightChecked)).Holds (lambdaReturns input initial) ↔ native) ∧
      (Rows.rtlObservation leftTargets.1 input initial = lambdaReturns input initial (scope rightChecked) ↔ native) := by
  have l := observations_eq leftChecked input initial
  have r := observations_eq rightChecked input initial
  have equality : ({result | result ∈ nativeDenote left input initial} : Rows.Observation) =
      {result | result ∈ nativeDenote right input initial} ↔
      left.denote model input = right.denote model input :=
    returnSets_eq_iff (left.denote model input) (right.denote model input) initial
  simp only [Sentence.Holds, l.1, l.2, r.1, r.2]
  exact ⟨equality, equality, equality⟩

theorem equation_holds_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (initial : Memory) :
    let native := (Loop.Institution.Sentence.equation (equation left right)).Holds model
    ((∀ input : WordTuple arity, (Sentence.eq leftTargets.1 rightTargets.1).Holds
        (fun target => Rows.rtlObservation target input initial)) ↔ native) ∧
      ((∀ input : WordTuple arity, (Sentence.eq (scope leftChecked) (scope rightChecked)).Holds
        (lambdaReturns input initial)) ↔ native) ∧
      ((∀ input : WordTuple arity, Rows.rtlObservation leftTargets.1 input initial =
        lambdaReturns input initial (scope rightChecked)) ↔ native) :=
  ⟨forall_congr' fun input => (equation_at_iff leftChecked rightChecked input initial).1,
    forall_congr' fun input => (equation_at_iff leftChecked rightChecked input initial).2.1,
    forall_congr' fun input => (equation_at_iff leftChecked rightChecked input initial).2.2⟩

theorem terminates_holds_iff (accepted : lowerChecked left = some leftTargets) (initial : Memory) :
    let native := (Loop.Institution.Sentence.terminates (program left)).Holds model
    ((∀ input : WordTuple arity, (Rows.rtlObservation leftTargets.1 input initial).Nonempty) ↔ native) ∧
      ((∀ input : WordTuple arity, (lambdaReturns input initial (scope accepted)).Nonempty) ↔ native) := by
  have returned (input : WordTuple arity) :
      ({ result | result ∈ nativeDenote left input initial } : Rows.Observation).Nonempty ↔
        (left.denote model input).Dom :=
    Part.dom_iff_mem.symm
  refine ⟨forall_congr' fun input => ?_, forall_congr' fun input => ?_⟩
  · rw [(observations_eq accepted input initial).1]
    exact returned input
  · rw [(observations_eq accepted input initial).2]
    exact returned input

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Proofs
