module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Traversal
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields (Route encode separatesWidths_of_distinct)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

variable {V F α : Type} [DecidableEq V] {a b : Nat}
variable {left right : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}
variable (first : Profile left inputs outputs) (second : Profile right inputs outputs)

theorem separates (model : PairModel F Part α) (values : ∃ x y : α, x ≠ y) :
    Separates inputs outputs model :=
  fun _ j => separatesWidths_of_distinct model (outputs j) values

private theorem compare_supported {n l r : Nat} (left : Outcome n l outputs) (right : Outcome n r outputs) :
    (left.refines? right).isSome ↔ left.supported ∧ right.supported := by
  cases left <;> cases right <;> simp [Outcome.refines?, Outcome.supported]

private theorem supported_iff :
    ((List.finRange a).map (fun input => (entryOutcome first input).refines? (entryOutcome second input))).all
      Option.isSome = true ↔ EntryTyped first ∧ EntryTyped second := by
  simp [List.all_eq_true, compare_supported, EntryTyped, forall_and]

theorem refinement_none :
    refinement? first second = none ↔ ¬ (EntryTyped first ∧ EntryTyped second) := by
  dsimp only [refinement?]
  split
  · rename_i supported
    simp [(supported_iff first second).mp supported]
  · rename_i unsupported
    simp [mt (supported_iff first second).mpr unsupported]

private theorem returns (model : PairModel F Part α) {graph : Graph V F a b} (profile : Profile graph inputs outputs) (input : Fin a)
    (packet : Fin (inputs input) → α) {port : Fin b} {fields : Route (inputs input) (outputs port)}
    (found : entryOutcome profile input = .returns port fields) :
    graph.denote model.val (input, encode model.val packet) =
      Part.some (port, encode model.val (packet ∘ fields)) :=
  entry_sound model profile input packet _ (by rw [found]; rfl)

private theorem cycle (model : PairModel F Part α) {graph : Graph V F a b} (profile : Profile graph inputs outputs) (input : Fin a)
    (packet : Fin (inputs input) → α) {index : Fin graph.locals} (found : entryOutcome profile input = .cycle index) :
    graph.denote model.val (input, encode model.val packet) = Part.none :=
  entry_sound model profile input packet _ (by rw [found]; rfl)

private theorem entry_sound_le (model : PairModel F Part α) (input : Fin a)
    (packet : Fin (inputs input) → α)
    (accepted : (entryOutcome first input).refines? (entryOutcome second input) = some true) :
    left.denote model.val (input, encode model.val packet) ≤ right.denote model.val (input, encode model.val packet) := by
  cases source : entryOutcome first input with
  | unsupported i => simp [source, Outcome.refines?] at accepted
  | cycle i =>
    rw [cycle model first input packet source]
    exact fun result member => (Part.notMem_none result member).elim
  | returns sourcePort sourceFields =>
    cases target : entryOutcome second input with
    | unsupported i => simp [source, target, Outcome.refines?] at accepted
    | cycle i => simp [source, target, Outcome.refines?] at accepted
    | returns targetPort targetFields =>
      by_cases same : sourcePort = targetPort
      · subst targetPort
        have equal : sourceFields = targetFields := by
          simpa [source, target, Outcome.refines?] using accepted
        rw [returns model first input packet source, returns model second input packet target, equal]
      · simp [source, target, Outcome.refines?, same] at accepted

private theorem entry_complete (model : PairModel F Part α) (separating : Separates inputs outputs model)
    (input : Fin a)
    (typedL : (entryOutcome first input).supported) (typedR : (entryOutcome second input).supported)
    (included : ∀ packet : Fin (inputs input) → α, left.denote model.val (input, encode model.val packet) ≤
      right.denote model.val (input, encode model.val packet)) :
    (entryOutcome first input).refines? (entryOutcome second input) = some true := by
  cases source : entryOutcome first input with
  | unsupported i =>
    rw [source] at typedL
    exact typedL.elim
  | cycle i =>
    cases target : entryOutcome second input with
    | unsupported j =>
      rw [target] at typedR
      exact typedR.elim
    | returns port fields => rfl
    | cycle j => rfl
  | returns port fields =>
    cases target : entryOutcome second input with
    | unsupported j =>
      rw [target] at typedR
      exact typedR.elim
    | cycle j =>
      let packet : Fin (inputs input) → α := fun _ => model.val.unit
      have atPacket := included packet
      rw [returns model first input packet source, cycle model second input packet target] at atPacket
      exact (Part.notMem_none _ (atPacket _ (Part.mem_some _))).elim
    | returns port' fields' =>
      have equal (packet : Fin (inputs input) → α) :
          (port, encode model.val (packet ∘ fields)) = (port', encode model.val (packet ∘ fields')) := by
        have atPacket := included packet
        rw [returns model first input packet source, returns model second input packet target] at atPacket
        exact Part.mem_some_iff.mp (atPacket _ (Part.mem_some _))
      have samePort : port = port' := congrArg Prod.fst (equal fun _ => model.val.unit)
      subst port'
      have sameFields := separating input port fields fields' (fun packet => congrArg Prod.snd (equal packet))
      simp [Outcome.refines?, sameFields]

private theorem accepted_iff :
    refinement? first second = some true ↔
      ∀ input, (entryOutcome first input).refines? (entryOutcome second input) = some true := by
  dsimp only [refinement?]
  split
  · simp [List.all_eq_true]
  · rename_i unsupported
    simp only [reduceCtorEq, false_iff]
    intro accepted
    apply unsupported
    simp [accepted]

theorem refinement_sound (model : PairModel F Part α)
    (accepted : refinement? first second = some true) :
    Sat inputs model left right :=
  fun input packet => entry_sound_le first second model input packet ((accepted_iff first second).mp accepted input)

theorem refinement_some (model : PairModel F Part α) (separating : Separates inputs outputs model)
    (verdict : Bool) :
    refinement? first second = some verdict ↔ (EntryTyped first ∧ EntryTyped second) ∧
      (verdict = true ↔ Sat inputs model left right) := by
  have agrees (typed : EntryTyped first ∧ EntryTyped second) :
      (∀ input, (entryOutcome first input).refines? (entryOutcome second input) = some true) ↔
        Sat inputs model left right :=
    ⟨fun accepted input packet => entry_sound_le first second model input packet (accepted input),
      fun included input => entry_complete first second model separating input (typed.1 input) (typed.2 input) (included input)⟩
  dsimp only [refinement?]
  split
  · rename_i supported
    have typed := (supported_iff first second).mp supported
    simp only [Option.some.injEq, typed, true_and]
    rw [← agrees typed]
    cases verdict <;> simp [List.all_eq_true]
  · rename_i unsupported
    simp [mt (supported_iff first second).mpr unsupported]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width
