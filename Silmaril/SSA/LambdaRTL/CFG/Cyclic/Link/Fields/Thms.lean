module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Block
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Traversal
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Refinement

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

open Comparison

variable {V K F α : Type} [DecidableEq V] {n a b : Nat}

/-- A symbolic copy/destructure block selects fields at its target's width. -/
theorem blockTo_evalJump {M : Type → Type} [Monad M] [LawfulMonad M] (model : PairModel F M α)
    (packet : Fin n → α) (width : K → Nat) (block : Block V K F) (store : V → α)
    {target : K} {route : Route n (width target)} (accepted : blockTo? n width block = some ⟨target, route⟩) :
    block.body.evalJump model.val (upd store block.param (encode model.val packet)) =
      pure (target, encode model.val (packet ∘ route)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.block_to_sound model packet width block store accepted

/-- A checked block returns the requested label and selected fields. The
lawful model need only undo constructed pairs, and other registers are arbitrary. -/
theorem block_evalJump {M : Type → Type} [Monad M] [LawfulMonad M] (model : PairModel F M α)
    (packet : Fin n → α) (block : Block V K F) (store : V → α) {target : K} {fields : FieldMap n}
    (accepted : block? n block = some (target, fields)) :
    block.body.evalJump model.val (upd store block.param (encode model.val packet)) =
      pure (target, encode model.val (packet ∘ fields)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.block_sound model packet block store accepted

/-- A supported outcome predicts actual CFG observations on packed inputs.
A repeated label yields `Part.none` because its checked successors stay
private and preserve packet shape, even when the payload changes. -/
theorem entryOutcome_sound (model : PairModel F Part α) (graph : Graph V F a b) (input : Fin a)
    (packet : Fin n → α) (result : Part (Fin b × α))
    (found : (entryOutcome n graph input).predict model.val packet = some result) :
    graph.denote model.val (input, encode model.val packet) = result :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.entry_sound model input packet result found

/-- Pair-lawfulness makes the packet encoding injective. Two field values
suffice to distinguish any two different field maps. -/
theorem separates_of_distinct (model : PairModel F Part α) (distinct : ∃ x y : α, x ≠ y) :
    Separates n model :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.separates model distinct

theorem separatesWidths_of_distinct (model : PairModel F Part α) (target : Nat) (distinct : ∃ x y : α, x ≠ y) :
    SeparatesWidths n target model :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.separates_widths model target distinct

/-- With zero output slots there is just one route. -/
theorem separatesWidths_zero (model : PairModel F Part α) : SeparatesWidths n 0 model :=
  fun _ _ _ => funext fun i => Fin.elim0 i

theorem refinement?_eq_none_iff (left right : Graph V F a b) :
    refinement? n left right = none ↔ ¬ (EntryTyped n left ∧ EntryTyped n right) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.refinement_none left right

theorem refinement_sound (model : PairModel F Part α) (left right : Graph V F a b)
    (accepted : refinement? n left right = some true) : Sat n model left right :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.refinement_sound model left right accepted

/-- On supported entries the verdict decides packet-restricted refinement
in a model that separates differing field maps. -/
theorem refinement?_eq_some_iff (model : PairModel F Part α) (separating : Separates n model)
    (left right : Graph V F a b) (verdict : Bool) :
    refinement? n left right = some verdict ↔ (EntryTyped n left ∧ EntryTyped n right) ∧
      (verdict = true ↔ Sat n model left right) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.refinement_some model separating left right verdict

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields
