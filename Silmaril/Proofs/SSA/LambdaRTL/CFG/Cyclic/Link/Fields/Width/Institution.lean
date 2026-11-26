module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Defs
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Institution.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width.Traversal
import Mathlib.Data.Finset.Card

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.Institution (LawfulModel)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Comparison
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution (ssaMapClass ssaClassObserve_map)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields (encode blockTo_mapOp)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width

variable {V K F F' α : Type} [DecidableEq V] {a b c n : Nat}
  {graph : Graph V F a b} {inputs : Fin a → Nat} {outputs : Fin b → Nat}

private theorem next_mapOp (profile : Profile graph inputs outputs) (rename : F → F')
    (index : Fin graph.locals) :
    next? (profile.mapOp rename) index = next? profile index :=
  blockTo_mapOp rename profile.width (graph.block index)

private theorem inspect_mapOp (profile : Profile graph inputs outputs) (rename : F → F')
    (remaining : Finset (Fin graph.locals)) (start : Label graph.locals b) :
    inspect (profile.mapOp rename) remaining start = inspect profile remaining start := by
  induction remaining using Finset.strongInductionOn generalizing start with
  | _ remaining ih =>
    refine (inspect.eq_def (profile.mapOp rename) remaining start).trans
      (Eq.trans ?_ (inspect.eq_def profile remaining start).symm)
    cases start with
    | inr port => rfl
    | inl index =>
      by_cases fresh : index ∈ remaining
      · simp only [dite_eq_left fresh, next_mapOp]
        erw [dite_eq_left fresh]
        cases checked : next? profile index with
        | none => rfl
        | some edge =>
          obtain ⟨target, route⟩ := edge
          exact congrArg (Outcome.precompose route) (ih _ (Finset.erase_ssubset fresh) target)
      · simp only [dite_eq_right fresh]
        erw [dite_eq_right fresh]
        rfl

theorem entry_mapOp (profile : Profile graph inputs outputs) (rename : F → F') (input : Fin a) :
    entryOutcome (profile.mapOp rename) input = entryOutcome profile input :=
  congrArg (Outcome.precompose (Fin.cast (profile.entryWidth input)))
    (inspect_mapOp profile rename Finset.univ (graph.entry input))

private theorem encode_reduct (rename : F → F') (model : PairModel F' Part α) (packet : Fin n → α) :
    encode (LawfulModel.reduct rename model).val packet = encode model.val packet := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change model.val.pair (packet 0) (encode (LawfulModel.reduct rename model).val (fun i : Fin n => packet i.succ)) =
      model.val.pair (packet 0) (encode model.val (fun i : Fin n => packet i.succ))
    rw [ih]

theorem packed_map [Inhabited V] [DecidableEq K] (rename : F → F') (model : PairModel F' Part α)
    (width : Nat) (lhs rhs : SSAClass V K F Part α) :
    packedSat width model (ssaMapClass rename lhs) (ssaMapClass rename rhs) ↔
      packedSat width (LawfulModel.reduct rename model) lhs rhs := by
  simp only [packedSat, ssaClassObserve_map, encode_reduct]

theorem compiled_packed_map [Inhabited V] (rename : F → F') (model : PairModel F' Part α)
    (width : Nat) (left right : Graph V F a b) (input : Fin a) :
    packedSat width model (namedSSAClass input (Quotient.mk _ (left.mapOp rename)))
        (namedSSAClass input (Quotient.mk _ (right.mapOp rename))) ↔
      packedSat width (LawfulModel.reduct rename model) (namedSSAClass input (Quotient.mk _ left))
        (namedSSAClass input (Quotient.mk _ right)) := by
  change packedSat width model (namedSSAClass input (mapArrow rename (Quotient.mk _ left)))
    (namedSSAClass input (mapArrow rename (Quotient.mk _ right))) ↔ _
  rw [namedSSAClass_mapArrow, namedSSAClass_mapArrow]
  exact packed_map rename model width _ _

private theorem returned_packet (model : PairModel F Part α) (profile : Profile graph inputs outputs)
    (typed : EntryTyped profile) (input : Fin a) (packet : Fin (inputs input) → α) {port : Fin b}
    {payload : α} (returned : (port, payload) ∈ graph.denote model.val (input, encode model.val packet)) :
    ∃ middle : Fin (outputs port) → α, payload = encode model.val middle := by
  cases found : entryOutcome profile input with
  | unsupported index =>
    have supported := typed input
    rw [found] at supported
    exact supported.elim
  | cycle index =>
    have empty := entry_sound model profile input packet Part.none (by rw [found]; rfl)
    exact (Part.notMem_none _ (empty ▸ returned)).elim
  | returns exit route =>
    have actual := entry_sound model profile input packet
      (Part.some (exit, encode model.val (packet ∘ route))) (by rw [found]; rfl)
    have equal := Part.mem_some_iff.mp (actual ▸ returned)
    have samePort : port = exit := congrArg Prod.fst equal
    subst exit
    exact ⟨packet ∘ route, congrArg Prod.snd equal⟩

theorem link_sat [Inhabited V] {left left' : Graph V F a b} {right right' : Graph V F b c}
    {mids : Fin b → Nat} (model : PairModel F Part α) (first : Profile left inputs mids)
    (typed : EntryTyped first) (leftSat : Sat inputs model left left') (rightSat : Sat mids model right right') :
    Sat inputs model (left.link right) (left'.link right') := by
  intro input packet result returned
  rw [Graph.denote_link] at returned ⊢
  obtain ⟨⟨port, payload⟩, produced, consumed⟩ := Part.mem_bind_iff.mp returned
  obtain ⟨middle, rfl⟩ := returned_packet model first typed input packet produced
  exact Part.mem_bind (leftSat input packet _ produced) (rightSat port middle _ consumed)

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Width
