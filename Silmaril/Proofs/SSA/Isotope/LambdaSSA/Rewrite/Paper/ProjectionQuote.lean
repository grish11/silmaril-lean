module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ProjectionQuote.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms

/-! # Native replay of projection quotes at arbitrary reply depth -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionQuote

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CaseTree.ReplyAgreement.NativeReplay (case_congr)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithCaseBind.OpenReplay
open CfgEta.TypeCategory (returnRegion_rename)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

local notation "Discards" => Paper.Extension.ReturnDiscards Seed

private theorem fst_discards (X A : Ty Empty) :
    Discards [product X A] (Term.fst (Φ := signature.Instr) X A).elaborate.val := by
  let e := Paper.WithProjectionReturns.Step.fst (Φ := signature.Instr) X A
  let h := (Term.fst (Φ := signature.Instr) X A).elaborate.property
  apply (Paper.Extension.returnDiscards_iff Seed h).2
  have eq := (Paper.Extension.Singleton.ofRegion_eq_iff Seed e.valueBranches.1 e.valueBranches.2).2
    (.extra e.valueBranches.1.hasType e.valueBranches.2.hasType (.inl (.inl (.inl (.inl e)))))
  change Paper.Extension.Singleton.ofRegion Seed e.valueBranches.1 ≫ _ = _
  rw [eq]
  exact Paper.Extension.Singleton.fst_discard Seed X A

theorem retainSlot_discards {X A : Ty Empty} (t : Term signature.Instr X Bit)
    (drop : Discards [X] t.elaborate.val) :
    Discards [product X A] (retainSlot (A := A) t).elaborate.val := by
  apply Paper.Extension.returnDiscards_let₁ Seed (Term.fst (Φ := signature.Instr) X A).elaborate.property
    (fst_discards X A)
  have moved := drop.renameVars ((Ren.wk [] (product X A)).lift X)
  rw [renameVars_lsubst, ← returnRegion_rename] at moved
  exact moved

theorem bindReply_discards {X : Ty Empty} {n : Nat} (slots : Fin n → Term signature.Instr X Bit)
    (drop : ∀ j, Discards [X] (slots j).elaborate.val) (i : Fin (n + 1)) :
    Discards [product X Bit] (bindReply slots i).elaborate.val := by
  cases i using Fin.cases with
  | zero => exact snd_discards X Bit
  | succ j => exact retainSlot_discards (slots j) (drop j)

theorem guardReplies_discards {X : Ty Empty} {n : Nat}
    (slots : Fin (n + 1) → Term signature.Instr X Bit)
    (drop : ∀ j, Discards [X] (slots j).elaborate.val) (test i : Fin (n + 1)) :
    Discards [product (product X unit) Bit] (guardReplies slots test i).elaborate.val :=
  bindReply_discards _ (fun j => retainSlot_discards _ (drop (test.succAbove j))) i

theorem readReply_discards (n : Nat) (i : Fin n) :
    Discards [replyContext n] (readReply n i).elaborate.val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih => exact bindReply_discards (readReply n) ih i

set_option backward.isDefEq.respectTransparency false in
theorem constant_quote {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (b : Bool) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit) (bits : List Bool)
    (drop : ∀ j, Discards [X] (slots j).elaborate.val) :
    selectedEq (selectTerminal pos (Finite.Expr.quote n (fun _ => b)) slots bits)
      (selectTerminal pos (.literal b) slots bits) := by
  induction n generalizing X bits with
  | zero => exact .refl (selectTerminal pos (.literal b) slots bits).elaborate.property.hasType
  | succ n ih =>
    let older (j : Fin n) := retainSlot (A := unit) (slots j.succ)
    have branch := ih older [] (fun j => retainSlot_discards _ (drop j.succ))
    have split : selectedEq (selectTerminal pos (Finite.Expr.quote (n + 1) (fun _ => b)) slots bits)
        (selectTerminal pos (.split (.literal b) (.literal b)) slots bits) :=
      case_congr (emitPrefix bits (slots 0)) branch branch
    exact split.trans (redundant_test (.literal b) pos slots bits (drop 0))

set_option backward.isDefEq.respectTransparency false in
theorem projection_quote {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (i : Fin n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit) (bits : List Bool)
    (drop : ∀ j, j ≠ i → Discards [X] (slots j).elaborate.val) :
    selectedEq (selectTerminal pos (Finite.Expr.quote n (fun env => env i)) slots bits)
      (selectTerminal pos (.read i) slots bits) := by
  induction n generalizing X bits with
  | zero => exact i.elim0
  | succ n ih =>
    let older (j : Fin n) := retainSlot (A := unit) (slots j.succ)
    cases i using Fin.cases with
    | zero =>
      have olderDrop (j : Fin n) : Discards [product X unit] (older j).elaborate.val :=
        retainSlot_discards _ (drop j.succ (Fin.succ_ne_zero j))
      have split : selectedEq (selectTerminal pos (Finite.Expr.quote (n + 1) (fun env => env 0)) slots bits)
          (selectTerminal pos (newestTable n) slots bits) :=
        case_congr (emitPrefix bits (slots 0))
          (constant_quote false pos older [] olderDrop) (constant_quote true pos older [] olderDrop)
      exact split.trans (newest_eq bits pos slots).symm
    | succ i =>
      have branch := ih i older []
        (fun j ne => retainSlot_discards _ (drop j.succ (fun eq => ne (Fin.succ_inj.mp eq))))
      have split : selectedEq (selectTerminal pos (Finite.Expr.quote (n + 1) (fun env => env i.succ)) slots bits)
          (selectTerminal pos (.split (.read i) (.read i)) slots bits) :=
        case_congr (emitPrefix bits (slots 0)) branch branch
      exact split.trans (redundant_test (.read i) pos slots bits (drop 0 (Ne.symm (Fin.succ_ne_zero i))))

theorem packed_projection_quote {L : List (Ty Empty)} {n : Nat}
    (i : Fin n) (pos : Position L) (bits : List Bool) :
    packed (.retExpr bits pos (Finite.Expr.quote n (fun env => env i))) = packed (.ret bits pos i) :=
  packed_congr (projection_quote i pos (readReply n) bits (fun j _ => readReply_discards n j))

set_option backward.isDefEq.respectTransparency false in
theorem quoteProjections_selectedWith {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    {X : Ty Empty} (slots : Fin n → Term signature.Instr X Bit)
    (drop : ∀ j, Discards [X] (slots j).elaborate.val) :
    selectedEq (p.quoteProjections.selectedWith slots) (p.selectedWith slots) := by
  induction p generalizing X with
  | ret emits pos i => exact projection_quote i pos slots emits (fun j _ => drop j)
  | retExpr emits pos e =>
    exact .refl (selectTerminal pos e slots emits).elaborate.property.hasType
  | request emits label bound _ _ il ir =>
    have next := bindReply_discards slots drop
    exact request_congr slots emits label bound bound (il _ next) (ir _ next)
  | testRequest emits test label low high _ _ _ _ ifl ifr itl itr =>
    have next := guardReplies_discards slots drop test
    exact testRequest_congr slots emits test label low high low high
      (ifl _ next) (ifr _ next) (itl _ next) (itr _ next)

theorem packed_quoteProjections {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) :
    packed p.quoteProjections = packed p :=
  packed_congr (quoteProjections_selectedWith p (readReply n) (readReply_discards n))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionQuote
