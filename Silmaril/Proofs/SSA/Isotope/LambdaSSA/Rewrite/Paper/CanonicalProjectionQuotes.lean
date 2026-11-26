module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.ProjectionQuotes.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ProjectionQuote.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

/-! # Exact recognition and native replay of live projection quotes -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalProjectionQuotes

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CaseTree.ReplyAgreement.NativeReplay (applyPacked_eqv case_congr)
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithCaseBind.OpenReplay
open Paper.WithCaseBind.OpenReplay.KnownGuardTraversal (requestTerm requestRegion retainPayload)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "E" => Paper.Extension.Eqv Seed
local notation "Discards" => Paper.Extension.ReturnDiscards Seed

private theorem quote_shape (n : Nat) (table : Finite.Table n) :
    hasFullQuoteShape (Finite.Expr.quote n table) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Finite.Expr.quote, hasFullQuoteShape, ih]

private theorem projection_quote_injective {n : Nat} {i j : Fin n}
    (h : (Finite.Expr.quote n fun row => row i) = Finite.Expr.quote n (fun row => row j)) : i = j := by
  have same := congrArg (fun e : Finite.Expr n => e.eval (fun k => decide (k = i))) h
  simp only [Finite.Expr.quote_eval] at same
  exact (of_decide_eq_true (same.symm.trans (by simp))).symm

theorem recognize_exact {n : Nat} (i : Fin n) :
    recognizeProjectionQuote (Finite.Expr.quote n (fun row => row i)) = some ⟨i, rfl⟩ := by
  have present : (recognizeProjectionQuote (Finite.Expr.quote n (fun row => row i))).isSome := by
    simp only [recognizeProjectionQuote, quote_shape, ↓reduceIte, List.findSome?_isSome_iff]
    exact ⟨i, by simp, by simp⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp present
  have index := projection_quote_injective q.property
  exact hq.trans (congrArg some (Subtype.ext index.symm))

theorem contract_idempotent {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) :
    p.contractProjectionQuotes.contractProjectionQuotes = p.contractProjectionQuotes := by
  induction p with
  | ret => rfl
  | retExpr _ _ e =>
    cases h : recognizeProjectionQuote e <;> simp [ReadTree.contractProjectionQuotes, h]
  | request _ _ _ _ _ hl hr => simp [ReadTree.contractProjectionQuotes, hl, hr]
  | testRequest _ _ _ _ _ _ _ _ _ hfl hfr htl htr =>
    simp [ReadTree.contractProjectionQuotes, hfl, hfr, htl, htr]

theorem contract_same_projection {X : Ty Empty} {L : List (Ty Empty)} {n m : Nat}
    (pos : Position L) (emits : List Bool)
    (left : Fin n → Term signature.Instr X Bit) (right : Fin m → Term signature.Instr X Bit)
    (i : Fin n) (j : Fin m) (same : left i = right j) :
    ((ReadTree.retExpr emits pos (Finite.Expr.quote n (fun row => row i))).contractProjectionQuotes).selectedWith left =
      (ReadTree.ret emits pos j).selectedWith right := by
  simp only [ReadTree.contractProjectionQuotes, recognize_exact, ReadTree.selectedWith]
  exact congrArg (fun t => selectTerminal pos (.read (0 : Fin 1)) (fun _ => t) emits) same

set_option backward.isDefEq.respectTransparency false in
theorem contract_selected {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    {X : Ty Empty} (slots : Fin n → Term signature.Instr X Bit)
    (drop : ∀ i, Discards [X] (slots i).elaborate.val) :
    selectedEq (p.selectedWith slots) (p.contractProjectionQuotes.selectedWith slots) := by
  induction p generalizing X with
  | ret => exact .refl (ReadTree.selectedWith _ slots).elaborate.property.hasType
  | retExpr emits pos e =>
    simp only [ReadTree.contractProjectionQuotes]
    cases recognizeProjectionQuote e with
    | none =>
      exact .refl (ReadTree.selectedWith _ slots).elaborate.property.hasType
    | some q =>
      obtain ⟨i, equation⟩ := q
      subst e
      exact projection_quote i pos slots emits (fun j _ => drop j)
  | request emits label bound _ _ hl hr =>
    exact case_congr _
      (hl (bindReply slots) (bindReply_discards slots drop))
      (hr (bindReply slots) (bindReply_discards slots drop))
  | testRequest emits test low lowBound highBound _ _ _ _ hfl hfr htl htr =>
    let next := guardReplies slots test
    have nextDrop := guardReplies_discards slots drop test
    exact case_congr _ (case_congr _ (hfl next nextDrop) (hfr next nextDrop))
      (case_congr _ (htl next nextDrop) (htr next nextDrop))

private theorem request_eqv {X : Ty Empty} {L : List (Ty Empty)}
    (a : Term signature.Instr X (coprod Bit Bit)) {l l' r r' : Region signature.Instr}
    (hl : E [product X Bit] l l' L) (hr : E [product X Bit] r r' L) :
    E [X] (requestRegion a l r) (requestRegion a l' r') L :=
  .case a.elaborate.property (applyPacked_eqv hl) (applyPacked_eqv hr)

set_option backward.isDefEq.respectTransparency false in
private theorem render_eqv {X : Ty Empty} {L : List (Ty Empty)} {n : Nat} {tag : Bool}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) (payload : Term signature.Instr X unit)
    (drop : ∀ i, Discards [X] (slots i).elaborate.val) :
    E [X] (c.pruned payload) (c.renderWith ReadTree.contractProjectionQuotes payload) L := by
  induction c with
  | @keep _ _ slots _ p => exact contract_selected p slots drop
  | @request _ _ slots _ _ _ emits label _ _ _ hl hr =>
    let carried := retainPayload (A := Bit) payload
    have nextDrop := bindReply_discards slots drop
    exact request_eqv (requestTerm emits label) (hl carried nextDrop) (hr carried nextDrop)
  | @guard Y _ slots _ _ _ _ _ emits test low _ _ _ _ _ _ hfl hfr htl htr =>
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    have nextDrop := guardReplies_discards slots drop test
    have lowEq := request_eqv (requestTerm (X := product Y unit) [] low)
      (hfl carried nextDrop) (hfr carried nextDrop)
    have highEq := request_eqv (requestTerm (X := product Y unit) [] (!low))
      (htl carried nextDrop) (htr carried nextDrop)
    exact .case (emitPrefix emits (slots test)).elaborate.property (applyPacked_eqv lowEq) (applyPacked_eqv highEq)
  | @prune Y _ slots _ _ _ _ _ emits test low _ _ _ _ _ hl hr =>
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    have nextDrop := guardReplies_discards slots drop test
    have liveEq := request_eqv (requestTerm (X := product Y unit) [] (if tag then !low else low))
      (hl carried nextDrop) (hr carried nextDrop)
    exact prependEmits_congr emits (.let₁ payload.elaborate.property (applyPacked_eqv liveEq))

theorem canonical_typed {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    ValueBranches [X] p.projectionCanonicalRegion L :=
  let payload := Term.snd (Φ := signature.Instr) X unit
  .case (emitPrefix p.split.emits (p.slots p.split.test).term).elaborate.property
    (applyPacked_typed_exits (p.traversal.onFalse.render_typed ReadTree.contractProjectionQuotes payload))
    (applyPacked_typed_exits (p.traversal.onTrue.render_typed ReadTree.contractProjectionQuotes payload))

private theorem normalized_canonical_eqv {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    E [X] p.normalized.val p.projectionCanonicalRegion L := by
  let payload := Term.snd (Φ := signature.Instr) X unit
  have drop (i : Fin p.width) :=
    retainSlot_discards (A := unit) (p.slots i).term (frameSlot_discards (p.slots i))
  exact .case (emitPrefix p.split.emits (p.slots p.split.test).term).elaborate.property
    (applyPacked_eqv (render_eqv p.traversal.onFalse payload drop))
    (applyPacked_eqv (render_eqv p.traversal.onTrue payload drop))

theorem packed_canonical {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    p.packedSource = Paper.Extension.Singleton.ofRegion Seed (canonical_typed p).packExits :=
  p.packed_normalized.trans ((Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    ((normalized_canonical_eqv p).lsubstPost p.normalized.property (canonical_typed p)
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalProjectionQuotes
