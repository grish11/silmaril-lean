module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Reindex.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Thms

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table

open CategoryTheory (Discrete)
open Silmaril.Isotope.Institution.Observational (Observation ssaBeh)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber (fiberRoom inputModel)
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Behavior Prog Result State Step Steps StepsNWithin run step)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (encodeTuple inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Logic.Institution.Observational (Sentence)
open Silmaril.Isotope.LambdaSSA.Semantics (Diverges)
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

private def identify : InputMap 3 := fun slot => if slot = 2 then 0 else slot
private def contracted := mapCaptures identify source

private theorem contractedHasTargets : (lowerChecked contracted).isSome := by
  obtain ⟨_, found⟩ := lowerChecked_mapCaptures identify accepted
  rw [show lowerChecked contracted = some _ from found]
  rfl

private def contractedTargets : Checked.Phi.Targets := (lowerChecked contracted).get contractedHasTargets
private theorem contractedAccepted : lowerChecked contracted = some contractedTargets := by cbv

example : identify 0 = identify 2 := by cbv
example : (contractedTargets.1.block? 0 0).map (·.ops) =
    some [.binary .sub (.arg 6) (.arg 0) (.arg 0), .binary .add (.arg 7) (.arg 6) (.arg 1)] := by cbv
example : (contractedTargets.1.block? 0 0).map (·.term) = some (.jump 1 [.arg 6, .arg 7, .arg 0]) := by cbv
example : contractedTargets.1.block? 0 1 = targets.1.block? 0 1 := by cbv

private def contractedInput := bank 5 2 6
example : identify.pull contractedInput = bank 5 2 5 := by cbv
example : contractedTargets.1.runMain 13 0 (words contractedInput) mem = .returned [6] mem := by cbv
example : Generic.Fuel.run model (inputEnv model contractedInput) 3 contractedTargets.2 =
    some (0, Generic.packResult model (out := word) (6 : Word)) := by cbv

private def contractedSpin := bank 1 0 42
private def equalCaptures := bank 1 0 1
private def zeroBank := bank 0 0 1

private theorem equalCapturesAbsent : source.denote model equalCaptures = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, returned⟩
  exact source.not_returns_of_backedge_invariant model equalCaptures value (· = zeroBank) (by cbv)
    (fun old fixed => fixed.symm ▸ ⟨zeroBank, by cbv, rfl⟩)
    ((source.returns_iff_mem_denote model _ _).mpr returned)

example :
    Behavior.diverges ∈ Institution.rtlBehaviors contractedSpin mem contractedTargets.1 ∧
      Observation.diverge mem ∈ ssaBeh 1
        (inputModel (P := Rows.wordSignature) model Memory contractedSpin) (Institution.scope contractedAccepted) := by
  obtain ⟨after, found, observes⟩ := reemit_mapped_observations identify accepted
  have same : after = contractedTargets := Option.some.inj (found.symm.trans contractedAccepted)
  subst after
  have agree := observes contractedSpin mem
  have pulled : identify.pull contractedSpin = equalCaptures := by cbv
  rw [pulled] at agree
  have old := (Institution.room_diverges_iff accepted equalCaptures mem).mpr equalCapturesAbsent
  exact ⟨agree.1 ▸ ((Institution.rtl_room_observation_iff accepted equalCaptures (.diverge mem)).mp old),
    agree.2 ▸ old⟩

private def aliasSubtraction : SourceWithEntry 3 Entry Header :=
  { source with
    preheader := .cons .sub (.cons (.arg (capture 2)) (.cons (.arg (capture 2)) .nil))
      (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg (capture 1)) .nil)) .nil) }

private def aliasPlan : Plan 3 Entry := (recognize aliasSubtraction).get (by cbv)
private theorem aliasRecognized : recognize aliasSubtraction = some aliasPlan := by cbv
private def aliasTargets : Checked.Phi.Targets := (aliasPlan.rtl, Generic.lower aliasSubtraction)
private theorem aliasAccepted : lowerChecked aliasSubtraction = some aliasTargets := by cbv

private theorem comparedGraphs : mapCaptures identify source = mapCaptures identify aliasSubtraction := by cbv
private theorem aliasMappedAccepted :
    lowerChecked (mapCaptures identify aliasSubtraction) = some contractedTargets := by
  rw [← comparedGraphs]
  exact contractedAccepted

private theorem differentAtInput : source.denote model input ≠ aliasSubtraction.denote model input := by
  intro same
  have lhs : source.denote model input = Part.some (7 : Word) :=
    Part.eq_some_iff.mpr ((source.returns_iff_mem_denote model input (7 : Word)).mp ⟨1, counted⟩)
  have rhs : aliasSubtraction.denote model input = Part.some (6 : Word) :=
    Part.eq_some_iff.mpr ((aliasSubtraction.returns_iff_mem_denote model input (6 : Word)).mp
      ((aliasSubtraction.returns_iff_evalBackedges model input (6 : Word)).mpr ⟨2, by cbv⟩))
  rw [lhs, rhs] at same
  exact (by decide : (7 : Word) ≠ 6) (Part.some_injective (α := Word) same)

example : ¬ (Loop.Institution.Sentence.equation (Institution.equation source aliasSubtraction)).Holds model :=
  fun holds => differentAtInput (holds input)

private theorem agreeOnImage : ∀ old ∈ Set.range (fun args : WordTuple 3 => identify.pull args),
    source.denote model old = aliasSubtraction.denote model old := by
  rintro _ ⟨args, rfl⟩
  exact (denote_mapCaptures identify recognized model args).symm.trans
    ((congrArg (fun graph => graph.denote model args) comparedGraphs).trans
      (denote_mapCaptures identify aliasRecognized model args))

example : input ∉ Set.range (fun args : WordTuple 3 => identify.pull args) :=
  fun pulled => differentAtInput (agreeOnImage input pulled)

example :
    (∀ args : WordTuple 3,
      (Sentence.eq contractedTargets.1 contractedTargets.1).Holds (Institution.rtlBehaviors args mem)) ∧
      (∀ args : WordTuple 3, (fiberRoom Rows.wordSignature (wordSorts 3).length).Sat
        (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory args))
        (Sentence.eq (Institution.scope contractedAccepted) (Institution.scope aliasMappedAccepted))) := by
  have laws := mapCaptures_equation_holds_iff identify accepted aliasAccepted
    contractedAccepted aliasMappedAccepted mem
  exact ⟨laws.1.mpr agreeOnImage, laws.2.mpr agreeOnImage⟩

private def removeCapture : InputMap 3 2 := fun slot => if slot = 1 then 1 else 0
private def narrowGraph : Width.Source 2 3 Entry Header := Width.mapCaptures removeCapture source
private def narrowTargets : Checked.Phi.Targets := (Width.lowerRTL narrowGraph, Generic.lower narrowGraph)
private theorem narrowAccepted : Width.lowerChecked removeCapture source = some narrowTargets :=
  Width.lowerChecked_of_accepted removeCapture accepted

example : (narrowTargets.1.func? 0).map (·.sig.params) = some 2 := by cbv
example : (narrowTargets.1.block? 0 0).map (·.ops) =
    some [.binary .sub (.arg 5) (.arg 0) (.arg 0), .binary .add (.arg 6) (.arg 5) (.arg 1)] := by cbv
example : (narrowTargets.1.block? 0 0).map (·.term) = some (.jump 1 [.arg 5, .arg 6, .arg 0]) := by cbv
example : (narrowTargets.1.block? 0 1).map (fun b => (b.params, b.term)) =
    some ([.arg 2, .arg 3, .arg 4], .cond (.node 1) 1 [.node 0, .arg 3, .arg 4] 2 [.node 0]) := by cbv

private def pair (a b : Word) : WordTuple 2 := .cons a (.cons b .nil)
private def narrowInput := pair 5 2
private def identifyPair : InputMap 2 1 := fun _ => 0

example (input : WordTuple 1) :
    InputMap.pull (identifyPair ∘ removeCapture) input = removeCapture.pull (identifyPair.pull input) :=
  InputMap.pull_comp removeCapture identifyPair input

example : removeCapture.pull narrowInput = bank 5 2 5 := by cbv
example : narrowGraph.initial model narrowInput = bank 0 2 5 := by cbv
example : ∃ start latched, narrowTargets.1.start 0 (words narrowInput) mem = some start ∧
    StepsNWithin narrowTargets.1 [] 3 start ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
    ArgsMatch latched (appendTuple (bank 0 2 5) narrowInput) := by
  obtain ⟨started, latched, steps, agreed⟩ := Width.checked_entry_packet removeCapture accepted narrowInput mem
  have initialized : source.initial model (removeCapture.pull narrowInput) = bank 0 2 5 := by cbv
  exact ⟨_, latched, started, steps, initialized ▸ agreed⟩

example : narrowTargets.1.runMain 13 0 (words narrowInput) mem = .returned [6] mem := by cbv
example : narrowTargets.1.runMain (Width.rtlFuel Entry Header 2) 0 (words narrowInput) mem =
    .returned [6] mem :=
  (Width.rtl_runMain_backedges_iff narrowAccepted narrowInput mem mem [6] 2).mpr
    ⟨6, by cbv, rfl, rfl⟩

example : (narrowTargets.1.runMain 12 0 (words narrowInput) mem).returnedValues? = none := by cbv
example : source.evalBackedges model 1 (removeCapture.pull narrowInput) = none := by cbv
example : narrowTargets.1.runMain 13 0 [5, 2, 5] mem = .stuck := by cbv
example : Generic.Fuel.run model (inputEnv model narrowInput) 3 narrowTargets.2 =
    some (0, Generic.packResult model (out := word) (6 : Word)) := by cbv

private def narrowSpin := pair 1 0

example : Diverges (instruction model) (.region (inputEnv model narrowSpin) narrowTargets.2 mem) :=
  (Width.lambda_diverges_iff narrowAccepted narrowSpin mem).mpr
    ((show removeCapture.pull narrowSpin = equalCaptures by cbv).symm ▸ equalCapturesAbsent)

private def runningState? : Result Reg → Option (State Reg)
  | .running state => some state
  | _ => none

private def narrowStart : State Reg := (narrowTargets.1.start 0 (words narrowSpin) mem).get (by cbv)
private def narrowHeader : State Reg := (runningState? (run narrowTargets.1 6 narrowStart)).get (by cbv)
private theorem reachesNarrowHeader : run narrowTargets.1 6 narrowStart = .running narrowHeader := by cbv

private theorem narrowCycle : run narrowTargets.1 3 narrowHeader = .running narrowHeader := by
  cbv
  congr 3
  funext r
  by_cases fourth : r = Reg.arg 4
  · simp [fourth]
  by_cases third : r = Reg.arg 3
  · simp [third]
  by_cases second : r = Reg.arg 2
  · simp [second]
  by_cases guard : r = Reg.node 1
  · simp [guard]
  by_cases value : r = Reg.node 0 <;> simp [fourth, third, second, guard, value]

private theorem steps_of_run {program : Prog Reg} {n : Nat} {s t : State Reg}
    (ran : run program n s = .running t) : Steps program s t := by
  induction n generalizing s with
  | zero =>
    have same : s = t := Result.running.inj ran
    exact same ▸ .refl
  | succ n ih =>
    unfold run at ran
    cases stepEq : step program s with
    | running next =>
      rw [stepEq] at ran
      exact .head stepEq (ih ran)
    | returned _ _ | trapped _ | stuck => rw [stepEq] at ran; cases ran

private theorem trace_of_cycle {program : Prog Reg} {s : State Reg} {n : Nat}
    (cycle : run program (n + 1) s = .running s) : Silmaril.Machine.RTL.SSA.Diverges program s := by
  let pending (t : State Reg) := ∃ k, run program k t = .running s
  have next {t : State Reg} {k : Nat} (path : run program (k + 1) t = .running s) :
      ∃ u, Step program t u ∧ pending u := by
    unfold run at path
    cases stepEq : step program t with
    | running u => rw [stepEq] at path; exact ⟨u, stepEq, k, path⟩
    | returned _ _ | trapped _ | stuck => rw [stepEq] at path; cases path
  apply InfiniteTrace.coinduct pending _ ⟨0, rfl⟩
  rintro t ⟨k, path⟩
  cases k with
  | zero =>
    have same : t = s := Result.running.inj path
    exact same.symm ▸ next cycle
  | succ k => exact next path

example : narrowTargets.1.divOracle 0 (words narrowSpin) mem :=
  ⟨narrowStart, by cbv, InfiniteTrace.of_steps (steps_of_run reachesNarrowHeader) (trace_of_cycle narrowCycle)⟩

example : ∀ returned final, ¬ narrowTargets.1.oracle 0 (words narrowSpin) mem returned final :=
  (Width.rtl_no_finite_return_iff narrowAccepted narrowSpin mem).mpr
    ((show removeCapture.pull narrowSpin = equalCaptures by cbv).symm ▸ equalCapturesAbsent)


example : (∀ args : WordTuple 2,
    narrowGraph.denote model args = (Width.mapCaptures removeCapture aliasSubtraction).denote model args) :=
  (Width.equation_on_image removeCapture source aliasSubtraction).mpr (by
    rintro _ ⟨args, rfl⟩
    have compared : Width.mapCaptures removeCapture source =
        Width.mapCaptures removeCapture aliasSubtraction := by cbv
    exact (Width.denote_mapCaptures removeCapture source model args).symm.trans
      ((congrArg (fun graph => graph.denote model args) compared).trans
        (Width.denote_mapCaptures removeCapture aliasSubtraction model args)))

-- The third source capture moves past an unused capture while the bank still has three lanes.
private def widenCaptures : InputMap 3 4 := fun slot => if slot = 2 then 3 else Fin.castLE (by decide) slot
private def wideGraph : Width.Source 4 3 Entry Header := Width.mapCaptures widenCaptures source
private def wideTargets : Checked.Phi.Targets := (Width.lowerRTL wideGraph, Generic.lower wideGraph)

private theorem wideAccepted : Width.lowerChecked widenCaptures source = some wideTargets :=
  Width.lowerChecked_of_accepted widenCaptures accepted

example : (wideTargets.1.func? 0).map (·.sig.params) = some 4 := by cbv
example : (wideTargets.1.block? 0 0).map (·.term) = some (.jump 1 [.arg 7, .arg 8, .arg 3]) := by cbv
example : (wideTargets.1.block? 0 1).map (·.params) = some [.arg 4, .arg 5, .arg 6] := by cbv

private def wideInput : WordTuple 4 := .cons (6 : Word) (bank 2 99 5)

example : widenCaptures.pull wideInput = input := by cbv
example : wideTargets.1.runMain 10 0 (words wideInput) mem = .returned [7] mem := by cbv
example : Generic.Fuel.run model (inputEnv model wideInput) 2 wideTargets.2 =
    some (0, Generic.packResult model (out := word) (7 : Word)) := by cbv

example : wideTargets.1.runMain (Width.rtlFuel Entry Header 1) 0 (words wideInput) mem =
    .returned [7] mem :=
  (Width.rtl_runMain_fuel_iff wideAccepted wideInput mem mem [7] _).mpr
    ⟨1, (7 : Word), (show widenCaptures.pull wideInput = input by cbv).symm ▸ counted, le_rfl, rfl, rfl⟩

private def wideImmediate : WordTuple 4 := .cons (9 : Word) (bank 2 99 5)

example : wideTargets.1.runMain (Width.rtlFuel Entry Header 0) 0 (words wideImmediate) mem =
    .returned [10] mem :=
  (Width.rtl_runMain_backedges_iff wideAccepted wideImmediate mem mem [10] 0).mpr
    ⟨10, by cbv, rfl, rfl⟩

private def wideSpin : WordTuple 4 := .cons (0 : Word) (bank 1 99 1)

example : wideTargets.1.divOracle 0 (words wideSpin) mem :=
  (Width.rtl_divOracle_iff wideAccepted wideSpin mem).mpr
    ((show widenCaptures.pull wideSpin = spin by cbv).symm ▸ spinAbsent)

private def dispatchSource : Width.Dispatch.Source 3 3 Entry Header :=
  ⟨source, .cons (.output (0 : Fin 2) .head)
    (.cons (.arg (old 2)) (.cons (.arg (old 1)) .nil)), .arg (prefixPort (capture 2))⟩

private def dispatchProg := Width.Dispatch.lowerRTL (Width.Dispatch.mapCaptures removeCapture dispatchSource)
private def otherTarget : Checked.Phi.Targets :=
  (Table.lowerChecked (dispatchSource.row false)).get (by cbv)

private theorem dispatchAccepted : Width.Dispatch.lowerChecked removeCapture dispatchSource = some dispatchProg :=
  Width.Dispatch.lowerChecked_of_accepted removeCapture dispatchSource
    (left := targets) (right := otherTarget) accepted (by cbv)

example : (dispatchProg.func? 0).map (·.sig.params) = some 2 :=
  (Width.Dispatch.lowerChecked_sound removeCapture dispatchSource dispatchAccepted).2.2.2

example : (dispatchProg.block? 0 3).map (·.term.args) =
    some [(1, [.node 0, .arg 3, .arg 4]), (1, [.node 0, .arg 4, .arg 3])] := by cbv

private def leftInput := narrowInput
private def rightInput := pair 0 (-1)

example : dispatchSource.step (removeCapture.pull leftInput) (bank 0 2 5) =
    .inr (true, bank 2 2 5) := by cbv
example : dispatchSource.step (removeCapture.pull rightInput) (bank 0 (-1) 0) =
    .inr (false, bank (-1) 0 (-1)) := by cbv

-- Observe the actual register bank after the first selected dispatcher transfer.
private def firstFeedback (input : WordTuple 2) : Option (Nat × List Word × Memory) := do
  let state ← runningState? (dispatchProg.runMain 7 0 (words input) mem)
  let values ← state.frame.readAll (paramRegs 2 3)
  pure (state.point.label, values, state.mem)

example : firstFeedback leftInput = some (1, [2, 2, 5], mem) := by cbv
example : firstFeedback rightInput = some (1, [-1, 0, -1], mem) := by cbv
example : dispatchProg.runMain 15 0 (words leftInput) mem = .returned [6] mem := by cbv
example : dispatchProg.runMain 11 0 (words rightInput) mem = .returned [-1] mem := by cbv
example : dispatchProg.runMain 15 0 (words (removeCapture.pull leftInput)) mem = .stuck := by cbv

private theorem rightCounted : dispatchSource.ReturnsAfter (removeCapture.pull rightInput) 1
    (source.initial model (removeCapture.pull rightInput)) (-1) :=
  .feedback (side := false) (next := bank (-1) 0 (-1)) (by cbv) (.exit (by cbv))

example : dispatchProg.oracle 0 (words rightInput) mem [-1] mem :=
  (Width.Dispatch.rtl_return_iff removeCapture dispatchSource dispatchAccepted rightInput mem mem [-1]).mpr
    ⟨1, -1, rightCounted, rfl, rfl⟩

example : (dispatchProg.runMain 10 0 (words rightInput) mem).returnedValues? = none := by cbv

-- The alternate projection must pass the same ordinary source checker.
example : Width.Dispatch.lowerChecked removeCapture { dispatchSource with
    other := .cons (.output (0 : Fin 2) .head)
      (.cons (.output (0 : Fin 2) .head) (.cons (.arg (old 1)) .nil)) } = none := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table
