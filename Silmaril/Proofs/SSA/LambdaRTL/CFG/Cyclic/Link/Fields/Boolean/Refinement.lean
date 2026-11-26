module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean.Traversal
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean

open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields (encode_injective)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width (Profile)

variable {V F α : Type} {a b n : Nat}

private theorem bit_injective (model : BooleanModel F α) : Function.Injective model.bit := by
  intro left right same
  have split := congrArg model.pairModel.val.split same
  cases left <;> cases right <;> simp [model.split_bit, Part.pure_eq_some] at split ⊢

private theorem render_injective (model : BooleanModel F α) {L : Type} {width : L → Nat} :
    Function.Injective (At.render (width := width) model) := by
  rintro ⟨left, packet⟩ ⟨right, packet'⟩ equal
  have same : left = right := congrArg Prod.fst equal
  subst right
  have payload : encodePacket model packet = encodePacket model packet' := congrArg Prod.snd equal
  have bits := encode_injective model.pairModel payload
  have samePacket : packet = packet' := funext fun i => bit_injective model (congrFun bits i)
  cases samePacket
  rfl

variable [DecidableEq V]
  {left right : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}

private theorem compare_supported {l r : Nat} {lw : Fin l → Nat} {rw : Fin r → Nat}
    (left : Outcome lw outputs) (right : Outcome rw outputs) :
    (left.refines? right).isSome ↔ left.supported ∧ right.supported := by
  cases left <;> cases right <;> simp [Outcome.refines?, Outcome.supported]

private theorem prediction_exists {localWidth : Fin n → Nat} (model : BooleanModel F α)
    (outcome : Outcome localWidth outputs) (supported : outcome.supported) :
    ∃ result, outcome.predict model = some result := by
  cases outcome with
  | returns result => exact ⟨_, rfl⟩
  | cycle state => exact ⟨_, rfl⟩
  | unsupported state => exact supported.elim

private theorem compare_prediction (model : BooleanModel F α) {l r : Nat}
    {lw : Fin l → Nat} {rw : Fin r → Nat}
    (left : Outcome lw outputs) (right : Outcome rw outputs) {p q : Part (Fin b × α)}
    (predictL : left.predict model = some p) (predictR : right.predict model = some q) :
    left.refines? right = some true ↔ p ≤ q := by
  cases left with
  | unsupported state => simp [Outcome.predict] at predictL
  | cycle state =>
    have same : Part.none = p := Option.some.inj predictL
    subst p
    have bottom : Part.none ≤ q := fun result present => (Part.notMem_none result present).elim
    cases right with
    | unsupported j => simp [Outcome.predict] at predictR
    | cycle j => exact ⟨fun _ => bottom, fun _ => rfl⟩
    | returns value => exact ⟨fun _ => bottom, fun _ => rfl⟩
  | returns source =>
    have same : Part.some (source.render model) = p := Option.some.inj predictL
    subst p
    cases right with
    | unsupported j => simp [Outcome.predict] at predictR
    | cycle j =>
      have same : Part.none = q := Option.some.inj predictR
      subst q
      simp only [Outcome.refines?, Option.some.injEq, Bool.false_eq_true, false_iff]
      exact fun included => Part.notMem_none _ (included _ (Part.mem_some _))
    | returns target =>
      have same : Part.some (target.render model) = q := Option.some.inj predictR
      subst q
      simp only [Outcome.refines?, Option.some.injEq, decide_eq_true_eq]
      exact ⟨fun equal => key_injective equal ▸ le_rfl, fun included =>
        congrArg At.key (render_injective model (Part.mem_some_iff.mp (included _ (Part.mem_some _))))⟩

theorem refinement_at (model : BooleanModel F α) (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (input : Fin a) (packet : Packet (inputs input))
    (typedL : (entryOutcome first input packet).supported) (typedR : (entryOutcome second input packet).supported) :
    refinementAt? first second input packet = some true ↔
      left.denote model.pairModel.val (input, encodePacket model packet) ≤
        right.denote model.pairModel.val (input, encodePacket model packet) := by
  obtain ⟨p, predictL⟩ := prediction_exists model _ typedL
  obtain ⟨q, predictR⟩ := prediction_exists model _ typedR
  rw [entry_sound model first input packet p predictL, entry_sound model second input packet q predictR]
  exact compare_prediction model _ _ predictL predictR

theorem refinement_at_none (first : Profile left inputs outputs) (second : Profile right inputs outputs)
    (input : Fin a) (packet : Packet (inputs input)) :
    refinementAt? first second input packet = none ↔
      ¬ ((entryOutcome first input packet).supported ∧ (entryOutcome second input packet).supported) := by
  unfold refinementAt?
  rw [← compare_supported]
  cases (entryOutcome first input packet).refines? (entryOutcome second input packet) <;> simp

private theorem all_results (first : Profile left inputs outputs) (second : Profile right inputs outputs)
    (test : Option Bool → Bool) :
    ((List.finRange a).flatMap fun input => (packets (inputs input)).map (refinementAt? first second input)).all test =
      true ↔ ∀ input packet, test (refinementAt? first second input packet) = true := by
  simp [List.all_eq_true, mem_packets]

private theorem supported_iff (first : Profile left inputs outputs) (second : Profile right inputs outputs) :
    ((List.finRange a).flatMap fun input => (packets (inputs input)).map (refinementAt? first second input)).all
      Option.isSome = true ↔ Supported first ∧ Supported second := by
  rw [all_results]
  simp only [refinementAt?, compare_supported, Supported, forall_and]

theorem refinement_none (first : Profile left inputs outputs) (second : Profile right inputs outputs) :
    refinement? first second = none ↔ ¬ (Supported first ∧ Supported second) := by
  dsimp only [refinement?]
  split
  · rename_i supported
    simp [(supported_iff first second).mp supported]
  · rename_i unsupported
    simp [mt (supported_iff first second).mpr unsupported]

theorem refinement_some (model : BooleanModel F α) (first : Profile left inputs outputs)
    (second : Profile right inputs outputs) (verdict : Bool) :
    refinement? first second = some verdict ↔ (Supported first ∧ Supported second) ∧
      (verdict = true ↔ Sat inputs model left right) := by
  dsimp only [refinement?]
  split
  · rename_i supported
    have typed := (supported_iff first second).mp supported
    have agrees : (∀ input packet, refinementAt? first second input packet = some true) ↔
        Sat inputs model left right :=
      forall_congr' fun input => forall_congr' fun packet =>
        refinement_at model first second input packet (typed.1 input packet) (typed.2 input packet)
    simp only [Option.some.injEq, typed, true_and]
    rw [← agrees]
    cases verdict <;> simp [mem_packets]
  · rename_i unsupported
    simp [mt (supported_iff first second).mpr unsupported]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Boolean
