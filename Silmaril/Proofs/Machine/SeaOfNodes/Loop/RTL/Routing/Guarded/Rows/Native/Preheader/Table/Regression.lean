module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table

open CategoryTheory (Discrete)
open Silmaril.Isotope.Institution.Observational (Observation ssaBeh)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber (fiberRoom inputModel)
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Behavior)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (encodeTuple inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Logic.Institution.Observational (Sentence)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def capture (slot : Fin 3) := argumentPort 3 slot
private def old (slot : Fin 3) := suffixPort (wordPorts 3) (capture slot)
private abbrev Entry := [[wordPort], [wordPort]]
private abbrev Header := [[wordPort], [.value .predicate]]

private def source : SourceWithEntry 3 Entry Header where
  preheader :=
    .cons .sub (.cons (.arg (capture 0)) (.cons (.arg (capture 2)) .nil))
      (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg (capture 1)) .nil)) .nil)
  header :=
    .cons .add (.cons (.arg (old 0)) (.cons (.arg (old 1)) .nil))
      (.cons .slt (.cons (.output (0 : Fin 1) .head) (.cons (.arg (old 2)) .nil)) .nil)
  phiInputs
    | .entry =>
      .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) (.cons (.arg (capture 2)) .nil))
    | .backedge =>
      .cons (.output (0 : Fin 2) .head) (.cons (.arg (old 1)) (.cons (.arg (old 2)) .nil))
  predicate := .output (1 : Fin 2) .head
  result := .output (0 : Fin 2) .head

private def rawStride : SourceWithEntry 3 Entry Header :=
  { source with
    phiInputs
      | .entry => .cons (.output (0 : Fin 2) .head) (.cons (.arg (capture 1)) (.cons (.arg (capture 2)) .nil))
      | .backedge => source.phiInputs .backedge }

example : lowerChecked { source with
    phiInputs
      | .entry => source.phiInputs .entry
      | .backedge =>
        .cons (.output (0 : Fin 2) .head)
          (.cons (.arg (prefixPort (capture 1))) (.cons (.arg (old 2)) .nil)) } = none := by cbv

example : lowerChecked { source with
    preheader := .cons .sub (.cons (.arg (capture 0)) (.cons (.arg (capture 2)) .nil))
      (.cons (.const 3) .nil .nil) } = none := by cbv

private def bank (x y z : Word) : WordTuple 3 := .cons x (.cons y (.cons z .nil))
private def input := bank 6 2 5
private def mem := Memory.ofList 4 [29, 71, 53, 11]

private def plan : Plan 3 Entry := (recognize source).get (by cbv)
private theorem recognized : recognize source = some plan := by cbv
private def targets : Checked.Phi.Targets := (plan.rtl, Generic.lower source)
private theorem accepted : lowerChecked source = some targets := by cbv

example : (targets.1.block? 0 0).map (·.ops) =
    some [.binary .sub (.arg 6) (.arg 0) (.arg 2), .binary .add (.arg 7) (.arg 6) (.arg 1)] := by cbv
example : (targets.1.block? 0 0).map (·.term) = some (.jump 1 [.arg 6, .arg 7, .arg 2]) := by cbv
example : (targets.1.block? 0 1).map (·.term) =
    some (.cond (.node 1) 1 [.node 0, .arg 4, .arg 5] 2 [.node 0]) := by cbv

example : source.initial model input = bank 1 3 5 := by cbv
example : rawStride.evalBackedges model 1 input = some (5 : Word) := by cbv

private theorem counted : source.ReturnsAfter model input 1 (source.initial model input) (7 : Word) :=
  .backedge (next := bank 4 3 5) (by cbv) (.exit (by cbv))

example : targets.1.runMain 10 0 (words input) mem = .returned [7] mem :=
  (rtl_runMain_fuel_iff recognized accepted _ _ _ _ _).mpr ⟨1, (7 : Word), counted, by decide, rfl, rfl⟩
private theorem rtlObserved : targets.1.runMain 10 0 (words input) mem = .returned [7] mem := by cbv
example : (targets.1.runMain 9 0 (words input) mem).returnedValues? = none := by cbv
private theorem lambdaObserved : Generic.Fuel.run model (inputEnv model input) 2 targets.2 =
    some (0, Generic.packResult model (out := word) (7 : Word)) := by cbv
example : Generic.Fuel.run model (inputEnv model input) 1 targets.2 = none := by cbv

example : targets.1.oracle 0 (words input) mem [7] mem :=
  (rtl_return_iff accepted _ _ _ _).mpr ⟨7, ⟨1, counted⟩, rfl, rfl⟩
example : Eval (instruction model) (inputEnv model input) targets.2 mem
    0 (Generic.packResult model (out := word) (7 : Word)) mem :=
  (lambda_return_iff accepted _ _ _ _ _).mpr ⟨7, ⟨1, counted⟩, rfl, rfl, rfl⟩

private theorem rtlDenoted : rtlDenote targets.1 input mem = Part.some (7, mem) :=
  Part.eq_some_iff.mpr ((mem_rtlDenote_iff_runMain _ _ _ _ _).mpr ⟨10, rtlObserved⟩)

private theorem nativeDenoted : nativeDenote source input mem = Part.some (7, mem) :=
  (denotations_eq accepted input mem).1.symm.trans rtlDenoted

example : lambdaDenote targets.2 input mem = Part.some (7, mem) :=
  Part.eq_some_iff.mpr ((mem_lambdaDenote_iff_run accepted _ _ _ _).mpr ⟨rfl, 2, lambdaObserved⟩)

private def spin := bank 0 1 1
private def fixedBank := bank (-1) 0 1

private theorem spinAbsent : source.denote model spin = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, returned⟩
  exact source.not_returns_of_backedge_invariant model spin value (· = fixedBank) (by cbv)
    (fun old fixed => fixed.symm ▸ ⟨fixedBank, by cbv, rfl⟩)
    ((source.returns_iff_mem_denote model _ _).mpr returned)

example :
    (∀ returned final, ¬ targets.1.oracle 0 (words spin) mem returned final) ∧
    (∀ label payload final, ¬ Eval (instruction model) (inputEnv model spin) targets.2 mem label payload final) :=
  let absence := no_finite_return_iff accepted spin mem
  ⟨absence.1.mpr spinAbsent, absence.2.mpr spinAbsent⟩

example : rtlDenote targets.1 spin mem = Part.none ∧ lambdaDenote targets.2 spin mem = Part.none :=
  let absence := denotations_none_iff accepted spin mem
  ⟨absence.1.mpr spinAbsent, absence.2.mpr spinAbsent⟩

example : (7, mem) ∈ Rows.rtlObservation targets.1 input mem ∧
    (7, mem) ∈ Institution.lambdaReturns input mem (Institution.scope accepted) := by
  have agree := Institution.observations_eq accepted input mem
  rw [agree.1, agree.2]
  exact ⟨Part.eq_some_iff.mp nativeDenoted, Part.eq_some_iff.mp nativeDenoted⟩

private def exitAtSpin : SourceWithEntry 3 Entry Header :=
  { source with
    preheader :=
      .cons .add (.cons (.arg (capture 0)) (.cons (.arg (capture 2)) .nil))
        (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg (capture 1)) .nil)) .nil) }

private def exitTargets : Checked.Phi.Targets := (lowerChecked exitAtSpin).get (by cbv)
private theorem exitAccepted : lowerChecked exitAtSpin = some exitTargets := by cbv

example : exitTargets.1.runMain 7 0 (words spin) mem = .returned [3] mem := by cbv

private theorem differs : exitAtSpin.denote model spin ≠ source.denote model spin := by
  rw [spinAbsent]
  intro absent
  have returned : exitAtSpin.Returns model spin (3 : Word) := ⟨0, .exit (by cbv)⟩
  have present := (exitAtSpin.returns_iff_mem_denote model spin (3 : Word)).mp returned
  rw [absent] at present
  exact Part.not_none_dom (Part.dom_iff_mem.mpr ⟨_, present⟩)

private theorem equationFails :
    ¬ (Loop.Institution.Sentence.equation (Institution.equation exitAtSpin source)).Holds model :=
  fun holds => differs (holds spin)

example :
    ¬ (∀ args : WordTuple 3, (Sentence.eq exitTargets.1 targets.1).Holds
        (fun target => Rows.rtlObservation target args mem)) ∧
    ¬ (∀ args : WordTuple 3, (Sentence.eq (Institution.scope exitAccepted) (Institution.scope accepted)).Holds
        (Institution.lambdaReturns args mem)) := by
  have agrees := Institution.equation_holds_iff exitAccepted accepted mem
  exact ⟨equationFails ∘ agrees.1.mp, equationFails ∘ agrees.2.1.mp⟩

private theorem terminationFails :
    ¬ (Loop.Institution.Sentence.terminates (Institution.program source)).Holds model :=
  fun holds => (Part.eq_none_iff'.mp spinAbsent) (holds spin)

example :
    ¬ (∀ args : WordTuple 3, (Rows.rtlObservation targets.1 args mem).Nonempty) ∧
    ¬ (∀ args : WordTuple 3, (Institution.lambdaReturns args mem (Institution.scope accepted)).Nonempty) := by
  have agrees := Institution.terminates_holds_iff accepted mem
  exact ⟨terminationFails ∘ agrees.1.mp, terminationFails ∘ agrees.2.mp⟩

example :
    let room := ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (Institution.scope accepted)
    let packet := Generic.packResult model (out := word) (7 : Word)
    Observation.ret mem (0, packet) mem ∈ room ∧ Observation.diverge mem ∉ room ∧
      Observation.ret mem (1, packet) mem ∉ room ∧ (∀ final, Observation.fault mem final ∉ room) := by
  have present := (source.returns_iff_mem_denote model input (7 : Word)).mp ⟨1, counted⟩
  exact ⟨(Institution.room_ret_iff accepted input mem mem 0 _).mpr ⟨7, present, rfl, rfl, rfl⟩,
    fun diverged => (Part.eq_none_iff'.mp ((Institution.room_diverges_iff accepted input mem).mp diverged))
      (Part.dom_iff_mem.mpr ⟨(7 : Word), present⟩),
    Institution.room_other_exit_absent accepted input mem mem 1 _ (by decide),
    Institution.room_fault_absent accepted input mem⟩

example :
    let room := ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory spin) (Institution.scope accepted)
    Observation.diverge mem ∈ room ∧ (∀ final, Observation.fault mem final ∉ room) :=
  ⟨(Institution.room_diverges_iff accepted spin mem).mpr spinAbsent,
    Institution.room_fault_absent accepted spin mem⟩

example :
    ¬ (fiberRoom Rows.wordSignature (wordSorts 3).length).Sat
      (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory spin))
      (Sentence.eq (Institution.scope exitAccepted) (Institution.scope accepted)) :=
  differs ∘ (Institution.room_equation_at_iff exitAccepted accepted spin mem).mp

example :
    let observed := Institution.rtlBehaviors input mem targets.1
    Behavior.returned [7] mem ∈ observed ∧ Behavior.diverges ∉ observed ∧
      Behavior.returned [7, 7] mem ∉ observed ∧ Behavior.stuck ∉ observed ∧
      (∀ final, Behavior.trapped final ∉ observed) := by
  have present := (source.returns_iff_mem_denote model input (7 : Word)).mp ⟨1, counted⟩
  refine ⟨(Institution.rtl_behavior_iff accepted input mem (.returned [7] mem)).mpr
    ⟨7, present, rfl, rfl⟩, ?_, ?_, Institution.rtl_no_fault accepted input mem⟩
  · intro diverged
    have absent := (Institution.rtl_divOracle_iff accepted input mem).mp diverged
    exact (Part.eq_none_iff'.mp absent) (Part.dom_iff_mem.mpr ⟨(7 : Word), present⟩)
  · intro unexpected
    obtain ⟨_, _, outputs, _⟩ :=
      (Institution.rtl_behavior_iff accepted input mem (.returned [7, 7] mem)).mp unexpected
    simp at outputs

example :
    targets.1.divOracle 0 (words spin) mem ∧
      (∀ values final, Behavior.returned values final ∉ Institution.rtlBehaviors spin mem targets.1) ∧
      Behavior.stuck ∉ Institution.rtlBehaviors spin mem targets.1 ∧
      (∀ final, Behavior.trapped final ∉ Institution.rtlBehaviors spin mem targets.1) := by
  refine ⟨(Institution.rtl_divOracle_iff accepted spin mem).mpr spinAbsent,
    ?_, Institution.rtl_no_fault accepted spin mem⟩
  intro values final returned
  obtain ⟨value, present, _, _⟩ :=
    (Institution.rtl_behavior_iff accepted spin mem (.returned values final)).mp returned
  exact (Part.eq_none_iff'.mp spinAbsent) (Part.dom_iff_mem.mpr ⟨value, present⟩)

example :
    ¬ (Sentence.eq exitTargets.1 targets.1).Holds (Institution.rtlBehaviors spin mem) :=
  differs ∘ (Institution.rtl_equation_at_iff exitAccepted accepted spin mem).mp

example :
    Behavior.returned [7] mem ∈ Institution.rtlBehaviors input mem targets.1 ∧
      Observation.ret mem (0, Generic.packResult model (out := word) (7 : Word)) mem ∈
        ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (Institution.scope accepted) := by
  have rtl : Behavior.returned [7] mem ∈ Institution.rtlBehaviors input mem targets.1 :=
    (mem_rtlDenote_iff _ _ _ _ _).mp (Part.eq_some_iff.mp rtlDenoted)
  exact ⟨rtl, (Institution.rtl_room_return_iff accepted input mem mem 7).mp rtl⟩

example :
    Behavior.diverges ∈ Institution.rtlBehaviors spin mem targets.1 ∧
      Observation.diverge mem ∈
        ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory spin) (Institution.scope accepted) := by
  have diverged := (Institution.room_diverges_iff accepted spin mem).mpr spinAbsent
  exact ⟨(Institution.rtl_room_observation_iff accepted spin (.diverge mem)).mp diverged, diverged⟩

example :
    Behavior.returned [3] mem ∈ Institution.rtlBehaviors spin mem exitTargets.1 ∧
      Observation.ret mem (0, Generic.packResult model (out := word) (3 : Word)) mem ∉
        ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory spin) (Institution.scope accepted) := by
  have returns : exitAtSpin.Returns model spin (3 : Word) := ⟨0, .exit (by cbv)⟩
  refine ⟨(rtl_return_iff exitAccepted spin mem mem [3]).mpr ⟨3, returns, rfl, rfl⟩, ?_⟩
  intro roomReturn
  have rtlReturn := (Institution.rtl_room_return_iff accepted spin mem mem 3).mpr roomReturn
  obtain ⟨value, present, _, _⟩ :=
    (Institution.rtl_behavior_iff accepted spin mem (.returned [3] mem)).mp rtlReturn
  exact (Part.eq_none_iff'.mp spinAbsent) (Part.dom_iff_mem.mpr ⟨value, present⟩)

example :
    ¬ (∀ args : WordTuple 3, (fiberRoom Rows.wordSignature (wordSorts 3).length).Sat
      (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory args))
      (Sentence.eq (Institution.scope exitAccepted) (Institution.scope accepted))) :=
  fun satisfies => differs ((Institution.rtl_equation_at_iff exitAccepted accepted spin mem).mp
    ((Institution.rtl_room_equation_holds_iff exitAccepted accepted mem).mpr satisfies spin))

private def swapCaptures : InputPermutation 3 := Equiv.swap 0 2
private def swappedSource := reindexCaptures swapCaptures source
private theorem swappedHasTargets : (lowerChecked swappedSource).isSome := by
  obtain ⟨_, found⟩ := lowerChecked_reindex swapCaptures accepted
  rw [show lowerChecked swappedSource = some _ from found]
  rfl

private def swappedTargets : Checked.Phi.Targets := (lowerChecked swappedSource).get swappedHasTargets
private theorem swappedAccepted : lowerChecked swappedSource = some swappedTargets := by cbv

private def rawEntry : SourceWithEntry 3 Entry Header :=
  { source with
    phiInputs
      | .entry => .cons (.arg (capture 0)) (.cons (.arg (capture 1)) (.cons (.arg (capture 2)) .nil))
      | .backedge => source.phiInputs .backedge }

private theorem rawRefused : lowerChecked rawEntry = none := by cbv

example : lowerChecked (reindexCaptures swapCaptures rawEntry) = none := by
  cases found : lowerChecked (reindexCaptures swapCaptures rawEntry) with
  | none => rfl
  | some targets =>
    obtain ⟨_, wasAccepted⟩ := (lowerChecked_reindex_iff swapCaptures (g := rawEntry)).mp ⟨targets, found⟩
    rw [rawRefused] at wasAccepted
    cases wasAccepted

example : (swappedTargets.1.block? 0 0).map (·.ops) =
    some [.binary .sub (.arg 6) (.arg 2) (.arg 0), .binary .add (.arg 7) (.arg 6) (.arg 1)] := by cbv
example : (swappedTargets.1.block? 0 0).map (·.term) = some (.jump 1 [.arg 6, .arg 7, .arg 0]) := by cbv
example : swappedTargets.1.block? 0 1 = targets.1.block? 0 1 := by cbv

private def swappedInput := bank 5 2 6
private def swappedSpin := bank 1 1 0

example : swapCaptures.pull swappedInput = input := by cbv
private theorem pullSpin : swapCaptures.pull swappedSpin = spin := by cbv
example : swappedTargets.1.runMain 10 0 (words swappedInput) mem = .returned [7] mem := by cbv
example : Generic.Fuel.run model (inputEnv model swappedInput) 2 swappedTargets.2 =
    some (0, Generic.packResult model (out := word) (7 : Word)) := by cbv
example : targets.1.runMain 7 0 (words swappedSpin) mem = .returned [3] mem := by cbv

example :
    Behavior.diverges ∈ Institution.rtlBehaviors swappedSpin mem swappedTargets.1 ∧
      Observation.diverge mem ∈ ssaBeh 1
        (inputModel (P := Rows.wordSignature) model Memory swappedSpin) (Institution.scope swappedAccepted) := by
  obtain ⟨after, found, observes⟩ := reemit_observations swapCaptures accepted
  have same : after = swappedTargets := Option.some.inj (found.symm.trans swappedAccepted)
  subst after
  have agree := observes swappedSpin mem
  rw [pullSpin] at agree
  have old := (Institution.room_diverges_iff accepted spin mem).mpr spinAbsent
  exact ⟨agree.1 ▸ ((Institution.rtl_room_observation_iff accepted spin (.diverge mem)).mp old),
    agree.2 ▸ old⟩

private def swappedExitTargets : Checked.Phi.Targets :=
  (lowerChecked (reindexCaptures swapCaptures exitAtSpin)).get (by cbv)

private theorem swappedExitAccepted :
    lowerChecked (reindexCaptures swapCaptures exitAtSpin) = some swappedExitTargets := by cbv

example : swappedExitTargets.1.runMain 7 0 (words swappedSpin) mem = .returned [3] mem := by cbv

example :
    ¬ (Sentence.eq swappedExitTargets.1 swappedTargets.1).Holds
      (Institution.rtlBehaviors swappedSpin mem) := by
  have agrees := reindex_equation_at_iff swapCaptures exitAccepted accepted
    swappedExitAccepted swappedAccepted swappedSpin mem
  intro holds
  have pulled := agrees.1.mp holds
  rw [pullSpin] at pulled
  exact differs pulled

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table
