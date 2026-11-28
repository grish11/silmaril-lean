module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.SelectedTerminal.Defs

/-! # Native replay on the actual open selected arrows -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The one-test table for the newest slot, with any older reply context. -/
abbrev newestTable (n : Nat) : Finite.Expr (n + 1) :=
  .split (.literal false) (.literal true)

abbrev selectedEq {X : Ty Empty} {L : List (Ty Empty)}
    (p q : CaseTree signature.Instr X L) : Prop :=
  Paper.Extension.Eqv Seed [X] p.elaborate.val q.elaborate.val L

/-- Pack the actual selected elaboration from its full native reply product. -/
def packed {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) :
    Paper.Extension.Singleton.ofType Seed (replyContext n) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed p.selected.elaborate.property.packExits

/-- Keep the untested slots in order and bind the chosen request's new reply. -/
abbrev guardReplies {X : Ty Empty} {n : Nat} (slots : Fin (n + 1) → Term signature.Instr X Bit)
    (test : Fin (n + 1)) : Fin (n + 1) → Term signature.Instr (product (product X unit) Bit) Bit :=
  bindReply (fun i => retainSlot (A := unit) (slots (test.succAbove i)))

/-- Replay the newest-bit read/table equation through the witnessed request
grammar. The request and guard labels and the ordered exits are shared.
Request-binder presentations may differ. -/
inductive Replay (L : List (Ty Empty)) : {n : Nat} → ReadTree L n → ReadTree L n → Prop where
  | refl {n : Nat} (p : ReadTree L n) : Replay L p p
  | symm {n : Nat} {p q : ReadTree L n} : Replay L p q → Replay L q p
  | trans {n : Nat} {p q r : ReadTree L n} : Replay L p q → Replay L q r → Replay L p r
  | newest {n : Nat} (emits : List Bool) (pos : Position L) :
      Replay L (.ret (n := n + 1) emits pos 0) (.retExpr emits pos (newestTable n))
  | request {n : Nat} (emits : List Bool) (label bound bound' : Bool) {l l' r r' : ReadTree L (n + 1)} :
      Replay L l l' → Replay L r r' →
      Replay L (.request emits label bound l r) (.request emits label bound' l' r')
  | testRequest {n : Nat} (emits : List Bool) (test : Fin (n + 1)) (label low high low' high' : Bool)
      {fl fl' fr fr' tl tl' tr tr' : ReadTree L (n + 1)} :
      Replay L fl fl' → Replay L fr fr' → Replay L tl tl' → Replay L tr tr' →
      Replay L (.testRequest emits test label low high fl fr tl tr)
        (.testRequest emits test label low' high' fl' fr' tl' tr')

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
