module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Block
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Traversal
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Refinement

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields

open Comparison

variable {V K F α : Type} [DecidableEq V] {n a b : Nat}

omit [DecidableEq V] in
theorem read?_eval {M : Type → Type} {model : Model F M α} {packet : Fin n → α}
    {env : V → Option (Val (Fin n))} {store : V → α} (agrees : StoreAgrees model packet env store)
    {value : Val V} {shape : Val (Fin n)} (found : read? env value = some shape) :
    value.eval model store = shape.eval model packet :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.read_eval agrees found

theorem StoreAgrees.update {M : Type → Type} {model : Model F M α} {packet : Fin n → α}
    {env : V → Option (Val (Fin n))} {store : V → α} (agrees : StoreAgrees model packet env store)
    (dst : V) (shape : Val (Fin n)) :
    StoreAgrees model packet (upd env dst (some shape)) (upd store dst (shape.eval model packet)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.agrees_upd agrees dst shape

theorem termTo_evalJump {M : Type → Type} [Monad M] (model : Model F M α)
    (packet : Fin n → α) (width : K → Nat) {env : V → Option (Val (Fin n))} {store : V → α}
    (agrees : StoreAgrees model packet env store) (term : Term V K F)
    {result : (target : K) × Route n (width target)} (accepted : termTo? width env term = some result) :
    (Body.term term).evalJump model store = pure (result.1, encode model (packet ∘ result.2)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.term_to_sound model packet width agrees term accepted

theorem blockWith_evalJump {M : Type → Type} [Monad M] [LawfulMonad M] (model : PairModel F M α)
    (packet : Fin n → α) {R : Type} (finish : (V → Option (Val (Fin n))) → Term V K F → Option R)
    (predict : R → K × α)
    (sound : ∀ env store term result, StoreAgrees model.val packet env store →
      finish env term = some result → (Body.term term).evalJump model.val store = pure (predict result))
    (block : Block V K F) (store : V → α) {result : R} (accepted : blockWith? n finish block = some result) :
    block.body.evalJump model.val (upd store block.param (encode model.val packet)) = pure (predict result) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.block_with_sound model packet finish predict sound block store accepted

/-- Primitive relabelling preserves the pure forwarding check. -/
theorem blockTo_mapOp {F' : Type} (rename : F → F') (width : K → Nat) (block : Block V K F) :
    blockTo? n width (block.mapOp rename) = blockTo? n width block :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.blockTo_mapOp rename width block

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

theorem encode_injective (model : PairModel F Part α) : Function.Injective (encode model.val (width := n)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.encode_injective model

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
