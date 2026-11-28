module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Discovery.Defs

/-! # Follow a known projection through requests and guards -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance traversalDefsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- A certificate indexed by the actual selected tree and the known tag.
Ordinary requests extend the frame. An unreduced guard certifies four
continuations. A reduced guard certifies only the two live reply arms. -/
inductive KnownGuardTraversal (L : List (Ty Empty)) (tag : Bool) :
    {X : Ty Empty} → {n : Nat} → (Fin n → Term signature.Instr X Bit) →
      Term signature.Instr X Bit → ReadTree L n → Type where
  | keep {X : Ty Empty} {n : Nat} {slots : Fin n → Term signature.Instr X Bit}
      {known : Term signature.Instr X Bit} (tree : ReadTree L n) : KnownGuardTraversal L tag slots known tree
  | request {X : Ty Empty} {n : Nat} {slots : Fin n → Term signature.Instr X Bit}
      {known : Term signature.Instr X Bit} {left right : ReadTree L (n + 1)} (emits : List Bool) (label bound : Bool)
      (leftCert : KnownGuardTraversal L tag (bindReply slots) (retainSlot (A := Bit) known) left)
      (rightCert : KnownGuardTraversal L tag (bindReply slots) (retainSlot (A := Bit) known) right) :
    KnownGuardTraversal L tag slots known (.request emits label bound left right)
  | guard {X : Ty Empty} {n : Nat} {slots : Fin (n + 1) → Term signature.Instr X Bit}
      {known : Term signature.Instr X Bit} {fl fr tl tr : ReadTree L (n + 1)}
      (emits : List Bool) (test : Fin (n + 1)) (low lowBound highBound : Bool)
      (fLeft : KnownGuardTraversal L tag (guardReplies slots test) (retainSlot (A := Bit) (retainSlot (A := unit) known)) fl)
      (fRight : KnownGuardTraversal L tag (guardReplies slots test) (retainSlot (A := Bit) (retainSlot (A := unit) known)) fr)
      (tLeft : KnownGuardTraversal L tag (guardReplies slots test) (retainSlot (A := Bit) (retainSlot (A := unit) known)) tl)
      (tRight : KnownGuardTraversal L tag (guardReplies slots test) (retainSlot (A := Bit) (retainSlot (A := unit) known)) tr) :
    KnownGuardTraversal L tag slots known (.testRequest emits test low lowBound highBound fl fr tl tr)
  | prune {X : Ty Empty} {n : Nat} {slots : Fin (n + 1) → Term signature.Instr X Bit}
      {known : Term signature.Instr X Bit} {fl fr tl tr : ReadTree L (n + 1)}
      (emits : List Bool) (test : Fin (n + 1)) (low lowBound highBound : Bool) (agreement : slots test = known)
      (left : KnownGuardTraversal L tag (guardReplies slots test) (retainSlot (A := Bit) (retainSlot (A := unit) known))
        (if tag then tl else fl))
      (right : KnownGuardTraversal L tag (guardReplies slots test) (retainSlot (A := Bit) (retainSlot (A := unit) known))
        (if tag then tr else fr)) :
    KnownGuardTraversal L tag slots known (.testRequest emits test low lowBound highBound fl fr tl tr)

namespace KnownGuardTraversal

/-- The selected request's exact discriminator. -/
def requestTerm {X : Ty Empty} (emits : List Bool) (label : Bool) : Term signature.Instr X (coprod Bit Bit) :=
  emitPrefix emits (.call (show signature.Instr from Op.ask label) .unit)

/-- The ordinary selected case shell around two already elaborated replies. -/
def requestRegion {X : Ty Empty} (a : Term signature.Instr X (coprod Bit Bit)) (l r : Region signature.Instr) :
    Region signature.Instr :=
  .case a.elaborate.val (Paper.PackedBody.applyPacked l) (Paper.PackedBody.applyPacked r)

/-- The prior case's payload remains a projection through a new right field. -/
def retainPayload {X A : Ty Empty} (p : Term signature.Instr X unit) :
    Term signature.Instr (product X A) unit :=
  .seq (.fst X A) p

/-- Compile the certificate with a supplied rewrite of the kept source
subtrees. Requests and pruned guards use their original continuation frames. -/
def renderWith {L : List (Ty Empty)} {tag : Bool} (rewriteKept : ∀ {n}, ReadTree L n → ReadTree L n) :
    {X : Ty Empty} → {n : Nat} → {slots : Fin n → Term signature.Instr X Bit} →
    {known : Term signature.Instr X Bit} → {p : ReadTree L n} →
    KnownGuardTraversal L tag slots known p → Term signature.Instr X unit → Region signature.Instr
  | _, _, slots, _, _, .keep p, _ => ((rewriteKept p).selectedWith slots).elaborate.val
  | X, _, _, _, _, .request emits label _ l r, payload =>
    let carried := retainPayload (A := Bit) payload
    requestRegion (requestTerm (X := X) emits label)
      (l.renderWith rewriteKept carried) (r.renderWith rewriteKept carried)
  | X, _ + 1, slots, _, _, .guard emits test low _ _ fl fr tl tr, payload =>
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    let lowArm := requestRegion (requestTerm (X := product X unit) [] low)
      (fl.renderWith rewriteKept carried) (fr.renderWith rewriteKept carried)
    let highArm := requestRegion (requestTerm (X := product X unit) [] (!low))
      (tl.renderWith rewriteKept carried) (tr.renderWith rewriteKept carried)
    .case (emitPrefix emits (slots test)).elaborate.val
      (Paper.PackedBody.applyPacked lowArm) (Paper.PackedBody.applyPacked highArm)
  | X, _ + 1, _, _, _, .prune emits _ low _ _ _ l r, payload =>
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    let live := requestRegion (requestTerm (X := product X unit) [] (if tag then !low else low))
      (l.renderWith rewriteKept carried) (r.renderWith rewriteKept carried)
    prependEmits emits (.let₁ payload.elaborate.val (Paper.PackedBody.applyPacked live))

/-- Compile the selected pruning certificate, keeping its other subtrees verbatim. -/
def pruned {L : List (Ty Empty)} {tag : Bool} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) (payload : Term signature.Instr X unit) :
    Region signature.Instr :=
  c.renderWith (fun p => p) payload

/-- A known projection survives the guard's slot deletion precisely when an
untested logical slot still reads it. The fresh reply is a distinct projection. -/
def guardSurvives {X : Ty Empty} {frame : ReplyFrame X} {n : Nat} (slots : Fin (n + 1) → ReplyFrame.Slot frame)
    (known : ReplyFrame.Slot frame) (test : Fin (n + 1)) : Bool :=
  (List.finRange n).any fun i => @decide _ (ReplyFrame.Slot.decEq frame (slots (test.succAbove i)) known)

/-- Traverse ordinary requests and guards on the literal structural frames.
After a guard loses the last slot for the carried bit, keep its reply subtrees. -/
def discover {L : List (Ty Empty)} :
    (tag : Bool) → {n : Nat} → (p : ReadTree L n) → {X : Ty Empty} → {frame : ReplyFrame X} →
    (slots : Fin n → ReplyFrame.Slot frame) → (known : ReplyFrame.Slot frame) →
    {terms : Fin n → Term signature.Instr X Bit} → {tested : Term signature.Instr X Bit} →
    (fun i => (slots i).term) = terms → known.term = tested → KnownGuardTraversal L tag terms tested p
  | _, _, .ret emits pos i, _, _, _, _, _, _, _, _ => .keep (.ret emits pos i)
  | _, _, .retExpr emits pos e, _, _, _, _, _, _, _, _ => .keep (.retExpr emits pos e)
  | tag, _, .request emits label bound left right, _, _, slots, known, _, _, slotTerms, testedTerm =>
    let nextTerms := (bindSlots_term slots).trans (congrArg bindReply slotTerms)
    let nextTest := congrArg (retainSlot (A := Bit)) testedTerm
    .request emits label bound
      (discover tag left (ReplyFrame.bindSlots slots) (.retainBit known) nextTerms nextTest)
      (discover tag right (ReplyFrame.bindSlots slots) (.retainBit known) nextTerms nextTest)
  | tag, _, .testRequest emits test low lowBound highBound fl fr tl tr, _, frame,
      slots, known, _, _, slotTerms, testedTerm =>
    let nextSlots := ReplyFrame.guardSlots slots test
    let nextKnown := ReplyFrame.Slot.retainBit (.retainUnit known)
    let nextTerms := (guardSlots_term slots test).trans (congrArg (fun slots => guardReplies slots test) slotTerms)
    let nextTest := congrArg (fun t => retainSlot (A := Bit) (retainSlot (A := unit) t)) testedTerm
    let survives := guardSurvives slots known test
    let visitFL := fun (_ : Unit) => if survives then discover tag fl nextSlots nextKnown nextTerms nextTest else .keep fl
    let visitFR := fun (_ : Unit) => if survives then discover tag fr nextSlots nextKnown nextTerms nextTest else .keep fr
    let visitTL := fun (_ : Unit) => if survives then discover tag tl nextSlots nextKnown nextTerms nextTest else .keep tl
    let visitTR := fun (_ : Unit) => if survives then discover tag tr nextSlots nextKnown nextTerms nextTest else .keep tr
    letI : Decidable (slots test = known) := ReplyFrame.Slot.decEq frame (slots test) known
    if h : slots test = known then
      have agreement := (congrFun slotTerms test).symm.trans ((congrArg ReplyFrame.Slot.term h).trans testedTerm)
      if hb : tag = true then
        .prune emits test low lowBound highBound agreement
          ((ite_eq_left hb).symm ▸ visitTL ()) ((ite_eq_left hb).symm ▸ visitTR ())
      else
        .prune emits test low lowBound highBound agreement
          ((ite_eq_right hb).symm ▸ visitFL ()) ((ite_eq_right hb).symm ▸ visitFR ())
    else
      .guard emits test low lowBound highBound (visitFL ()) (visitFR ()) (visitTL ()) (visitTR ())

end KnownGuardTraversal

/-- Both differently tagged certificates for the original outer split. -/
structure GuardSplitTraversal {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    (p : SelectedGuardSplit L n) (terms : Fin n → Term signature.Instr X Bit) where
  onFalse : KnownGuardTraversal L false (fun j => retainSlot (A := unit) (terms j))
    (retainSlot (terms p.test)) p.onFalse
  onTrue : KnownGuardTraversal L true (fun j => retainSlot (A := unit) (terms j))
    (retainSlot (terms p.test)) p.onTrue

def GuardSplitTraversal.renderWith {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {p : SelectedGuardSplit L n} {terms : Fin n → Term signature.Instr X Bit}
    (t : GuardSplitTraversal p terms)
    (rewriteKept : ∀ {n}, ReadTree L n → ReadTree L n) : Region signature.Instr :=
  let payload := Term.snd (Φ := signature.Instr) X unit
  .case (emitPrefix p.emits (terms p.test)).elaborate.val
    (Paper.PackedBody.applyPacked (t.onFalse.renderWith rewriteKept payload))
    (Paper.PackedBody.applyPacked (t.onTrue.renderWith rewriteKept payload))

def GuardSplitTraversal.pruned {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {p : SelectedGuardSplit L n} {terms : Fin n → Term signature.Instr X Bit}
    (t : GuardSplitTraversal p terms) : Region signature.Instr :=
  t.renderWith (fun p => p)

/-- Discover on an exact structural slot map. It may present multiple logical
slots reading the same field, and each guard removes only its tested slot. -/
def SelectedGuardSplit.traverseWith {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : SelectedGuardSplit L n) (slots : Fin n → ReplyFrame.Slot frame)
    {terms : Fin n → Term signature.Instr X Bit} (mapEq : (fun j => (slots j).term) = terms) :
    GuardSplitTraversal p terms :=
  let retained := fun j => ReplyFrame.Slot.retainUnit (slots j)
  have retainedEq : (fun j => (retained j).term) = fun j => retainSlot (A := unit) (terms j) :=
    congrArg (fun read j => retainSlot (A := unit) (read j)) mapEq
  ⟨KnownGuardTraversal.discover false p.onFalse retained (retained p.test) retainedEq (congrFun retainedEq p.test),
    KnownGuardTraversal.discover true p.onTrue retained (retained p.test) retainedEq (congrFun retainedEq p.test)⟩

/-- Discover on the original selected compiler's standard open input. -/
def SelectedGuardSplit.traverse {L : List (Ty Empty)} {n : Nat} (p : SelectedGuardSplit L n) :
    GuardSplitTraversal p (readReply n) :=
  p.traverseWith (ReplyFrame.standardSlots n) (standardSlots_term n)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
