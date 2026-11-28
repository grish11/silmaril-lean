module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ProjectionQuote.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ProjectionQuote

/-! # Native replay of projection quotes at arbitrary reply depth -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance projectionQuoteHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

local notation "Discards" => Paper.Extension.ReturnDiscards Seed

/-- A slot retains its discard certificate under the compiler's left
projection from a packed continuation input. -/
theorem retainSlot_discards {X A : Ty Empty} (t : Term signature.Instr X Bit)
    (drop : Discards [X] t.elaborate.val) :
    Discards [product X A] (retainSlot (A := A) t).elaborate.val :=
  ProjectionQuote.retainSlot_discards t drop

/-- Binding a reply adds a discardable projection and preserves discard for
each older slot. -/
theorem bindReply_discards {X : Ty Empty} {n : Nat} (slots : Fin n → Term signature.Instr X Bit)
    (drop : ∀ j, Discards [X] (slots j).elaborate.val) (i : Fin (n + 1)) :
    Discards [product X Bit] (bindReply slots i).elaborate.val :=
  ProjectionQuote.bindReply_discards slots drop i

/-- Deleting the tested slot, retaining the other slots through the unit
binder, and binding the next reply preserve the slot certificates. -/
theorem guardReplies_discards {X : Ty Empty} {n : Nat}
    (slots : Fin (n + 1) → Term signature.Instr X Bit)
    (drop : ∀ j, Discards [X] (slots j).elaborate.val) (test i : Fin (n + 1)) :
    Discards [product (product X unit) Bit] (guardReplies slots test i).elaborate.val :=
  ProjectionQuote.guardReplies_discards slots drop test i

/-- Every projection in the standard retained input map admits native discard. -/
theorem readReply_discards (n : Nat) (i : Fin n) :
    Discards [replyContext n] (readReply n i).elaborate.val :=
  ProjectionQuote.readReply_discards n i

/-- A full constant quote can omit every test when each slot admits native
discard. The emit prefix and typed position remain part of the return. -/
theorem constant_quote {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (b : Bool) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit) (bits : List Bool)
    (drop : ∀ j, Discards [X] (slots j).elaborate.val) :
    selectedEq (selectTerminal pos (Finite.Expr.quote n (fun _ => b)) slots bits)
      (selectTerminal pos (.literal b) slots bits) :=
  ProjectionQuote.constant_quote b pos slots bits drop

/-- Compile the full quote of any slot as a single read, keeping the emit
prefix and typed exit. Discard is required only for the other slots. -/
theorem projection_quote {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (i : Fin n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit) (bits : List Bool)
    (drop : ∀ j, j ≠ i → Discards [X] (slots j).elaborate.val) :
    selectedEq (selectTerminal pos (Finite.Expr.quote n (fun env => env i)) slots bits)
      (selectTerminal pos (.read i) slots bits) :=
  ProjectionQuote.projection_quote i pos slots bits drop

/-- The projection quote and the direct read are equal as actual packed
arrows from the full retained reply product. -/
theorem packed_projection_quote {L : List (Ty Empty)} {n : Nat}
    (i : Fin n) (pos : Position L) (bits : List Bool) :
    packed (.retExpr bits pos (Finite.Expr.quote n (fun env => env i))) = packed (.ret bits pos i) :=
  ProjectionQuote.packed_projection_quote i pos bits

/-- Expand direct returns under arbitrary request and retained-bit test
nesting, using the actual reindexed continuation slots at every guard. -/
theorem quoteProjections_selectedWith {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    {X : Ty Empty} (slots : Fin n → Term signature.Instr X Bit)
    (drop : ∀ j, Discards [X] (slots j).elaborate.val) :
    selectedEq (p.quoteProjections.selectedWith slots) (p.selectedWith slots) :=
  ProjectionQuote.quoteProjections_selectedWith p slots drop

/-- The full-tree replay gives equality on the actual selected packed arrows
before specializing the retained assignment. -/
theorem packed_quoteProjections {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) :
    packed p.quoteProjections = packed p :=
  ProjectionQuote.packed_quoteProjections p

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
