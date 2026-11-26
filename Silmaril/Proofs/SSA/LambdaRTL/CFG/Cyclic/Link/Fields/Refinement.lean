module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Traversal

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

variable {V F α : Type} {n a b : Nat}

private theorem encode_injective (model : PairModel F Part α) :
    Function.Injective (encode model.val (width := n)) := by
  induction n with
  | zero =>
    intro left right _
    exact funext fun i => Fin.elim0 i
  | succ n ih =>
    intro left right same
    have products := congrArg model.val.unpair same
    simp only [encode, model.property.unpair_pair, Part.pure_eq_some, Part.some_inj] at products
    funext i
    refine Fin.cases (congrArg Prod.fst products) (fun j => ?_) i
    exact congrFun (ih (congrArg Prod.snd products)) j

theorem separates_widths (model : PairModel F Part α) (target : Nat) (values : ∃ x y : α, x ≠ y) :
    SeparatesWidths n target model := by
  obtain ⟨x, y, distinct⟩ := values
  intro left right same
  funext i
  by_contra different
  let packet : Fin n → α := fun j => if j = left i then x else y
  have observed := congrFun (encode_injective model (same packet)) i
  exact distinct (by simpa [packet, Function.comp_def, Ne.symm different] using observed)

theorem separates (model : PairModel F Part α) (values : ∃ x y : α, x ≠ y) :
    Separates n model :=
  separates_widths model n values

variable [DecidableEq V]

private theorem compare_supported {l r : Nat} (left : Outcome n l b) (right : Outcome n r b) :
    (left.refines? right).isSome ↔ left.supported ∧ right.supported := by
  cases left <;> cases right <;> simp [Outcome.refines?, Outcome.supported]

private theorem supported_iff (left right : Graph V F a b) :
    ((List.finRange a).map (fun input => (entryOutcome n left input).refines? (entryOutcome n right input))).all
      Option.isSome = true ↔ EntryTyped n left ∧ EntryTyped n right := by
  simp [List.all_eq_true, compare_supported, EntryTyped, forall_and]

theorem refinement_none (left right : Graph V F a b) :
    refinement? n left right = none ↔ ¬ (EntryTyped n left ∧ EntryTyped n right) := by
  dsimp only [refinement?]
  split
  · rename_i supported
    simp [(supported_iff left right).mp supported]
  · rename_i unsupported
    simp [mt (supported_iff left right).mpr unsupported]

private theorem returns (model : PairModel F Part α) (graph : Graph V F a b) (input : Fin a)
    (packet : Fin n → α) {port : Fin b} {fields : FieldMap n}
    (found : entryOutcome n graph input = .returns port fields) :
    graph.denote model.val (input, encode model.val packet) =
      Part.some (port, encode model.val (packet ∘ fields)) :=
  entry_sound model input packet _ (by rw [found]; rfl)

private theorem cycle (model : PairModel F Part α) (graph : Graph V F a b) (input : Fin a)
    (packet : Fin n → α) {index : Fin graph.locals} (found : entryOutcome n graph input = .cycle index) :
    graph.denote model.val (input, encode model.val packet) = Part.none :=
  entry_sound model input packet _ (by rw [found]; rfl)

private theorem entry_sound_le (model : PairModel F Part α) (left right : Graph V F a b) (input : Fin a)
    (packet : Fin n → α)
    (accepted : (entryOutcome n left input).refines? (entryOutcome n right input) = some true) :
    left.denote model.val (input, encode model.val packet) ≤ right.denote model.val (input, encode model.val packet) := by
  cases source : entryOutcome n left input with
  | unsupported i => simp [source, Outcome.refines?] at accepted
  | cycle i =>
    rw [cycle model left input packet source]
    exact fun result member => (Part.notMem_none result member).elim
  | returns sourcePort sourceFields =>
    cases target : entryOutcome n right input with
    | unsupported i => simp [source, target, Outcome.refines?] at accepted
    | cycle i => simp [source, target, Outcome.refines?] at accepted
    | returns targetPort targetFields =>
      have same : sourcePort = targetPort ∧ sourceFields = targetFields := by
        simpa [source, target, Outcome.refines?] using accepted
      rw [returns model left input packet source, returns model right input packet target, same.1, same.2]

private theorem entry_complete (model : PairModel F Part α) (separating : Separates n model)
    (left right : Graph V F a b) (input : Fin a)
    (typedL : (entryOutcome n left input).supported) (typedR : (entryOutcome n right input).supported)
    (included : ∀ packet : Fin n → α, left.denote model.val (input, encode model.val packet) ≤
      right.denote model.val (input, encode model.val packet)) :
    (entryOutcome n left input).refines? (entryOutcome n right input) = some true := by
  cases source : entryOutcome n left input with
  | unsupported i =>
    rw [source] at typedL
    exact typedL.elim
  | cycle i =>
    cases target : entryOutcome n right input with
    | unsupported j =>
      rw [target] at typedR
      exact typedR.elim
    | returns port fields => rfl
    | cycle j => rfl
  | returns port fields =>
    cases target : entryOutcome n right input with
    | unsupported j =>
      rw [target] at typedR
      exact typedR.elim
    | cycle j =>
      let packet : Fin n → α := fun _ => model.val.unit
      have atPacket := included packet
      rw [returns model left input packet source, cycle model right input packet target] at atPacket
      exact (Part.notMem_none _ (atPacket _ (Part.mem_some _))).elim
    | returns port' fields' =>
      have equal (packet : Fin n → α) :
          (port, encode model.val (packet ∘ fields)) = (port', encode model.val (packet ∘ fields')) := by
        have atPacket := included packet
        rw [returns model left input packet source, returns model right input packet target] at atPacket
        exact Part.mem_some_iff.mp (atPacket _ (Part.mem_some _))
      have samePort : port = port' := congrArg Prod.fst (equal fun _ => model.val.unit)
      have sameFields := separating fields fields' (fun packet => congrArg Prod.snd (equal packet))
      simp [Outcome.refines?, samePort, sameFields]

private theorem accepted_iff (left right : Graph V F a b) :
    refinement? n left right = some true ↔
      ∀ input, (entryOutcome n left input).refines? (entryOutcome n right input) = some true := by
  dsimp only [refinement?]
  split
  · simp [List.all_eq_true]
  · rename_i unsupported
    simp only [reduceCtorEq, false_iff]
    intro accepted
    apply unsupported
    simp [accepted]

theorem refinement_sound (model : PairModel F Part α) (left right : Graph V F a b)
    (accepted : refinement? n left right = some true) :
    Sat n model left right :=
  fun input packet => entry_sound_le model left right input packet ((accepted_iff left right).mp accepted input)

theorem refinement_some (model : PairModel F Part α) (separating : Separates n model)
    (left right : Graph V F a b) (verdict : Bool) :
    refinement? n left right = some verdict ↔ (EntryTyped n left ∧ EntryTyped n right) ∧
      (verdict = true ↔ Sat n model left right) := by
  have agrees (typed : EntryTyped n left ∧ EntryTyped n right) :
      (∀ input, (entryOutcome n left input).refines? (entryOutcome n right input) = some true) ↔
        Sat n model left right :=
    ⟨fun accepted input packet => entry_sound_le model left right input packet (accepted input),
      fun included input => entry_complete model separating left right input (typed.1 input) (typed.2 input) (included input)⟩
  dsimp only [refinement?]
  split
  · rename_i supported
    have typed := (supported_iff left right).mp supported
    simp only [Option.some.injEq, typed, true_and]
    rw [← agrees typed]
    cases verdict <;> simp [List.all_eq_true]
  · rename_i unsupported
    simp [mt (supported_iff left right).mpr unsupported]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields
