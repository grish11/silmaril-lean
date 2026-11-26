module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.PacketCases.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Syntax.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RedundantSelectedTest

/-! # Removing one redundant selected table test -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance redundantTestHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

local notation "E" => Paper.Extension.Eqv Seed

/-- Equal regions stay equal below the same ordered emit prefix. -/
theorem prependEmits_congr {Γ L : List (Ty Empty)} {r s : Region signature.Instr}
    (bits : List Bool) (h : E Γ r s L) : E Γ (prependEmits bits r) (prependEmits bits s) L :=
  RedundantSelectedTest.prependEmits_congr bits h

/-- The selected terminal executes its emits before entering the terminal on
the original input, in the order of the supplied list. -/
theorem terminal_prefix {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit) (bits : List Bool) :
    E [X] (selectTerminal pos e slots bits).elaborate.val
      (prependEmits bits (selectTerminal pos e slots []).elaborate.val) L :=
  RedundantSelectedTest.terminal_prefix e pos slots bits

/-- Opening the packed unit binder over the retained input gives ordinary
lexical weakening of the selected terminal. -/
theorem terminal_weakening {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (pos : Position L) (slots : Fin n → Term signature.Instr X Bit) :
    E [unit, X]
      (Paper.PackedBody.applyPacked (selectTerminal pos e (fun i => retainSlot (A := unit) (slots i)) []).elaborate.val)
      ((selectTerminal pos e slots []).elaborate.val.renameVars Nat.succ) L :=
  RedundantSelectedTest.terminal_weakening e pos slots

/-- An identical-arm test can be removed if the unprefixed discriminator
return discards in the native quotient. The common emit prefix is retained. -/
theorem redundant_test {X : Ty Empty} {L : List (Ty Empty)} {n : Nat}
    (e : Finite.Expr n) (pos : Position L) (slots : Fin (n + 1) → Term signature.Instr X Bit)
    (bits : List Bool) (drop : Paper.Extension.ReturnDiscards Seed [X] (slots 0).elaborate.val) :
    selectedEq (selectTerminal pos (.split e e) slots bits)
      (selectTerminal pos e (fun i => slots i.succ) bits) :=
  RedundantSelectedTest.redundant_test e pos slots bits drop

/-- Returning the second projection from a product input admits native discard. -/
theorem snd_discards (X D : Ty Empty) :
    Paper.Extension.ReturnDiscards Seed [product X D] (Term.snd (Φ := signature.Instr) X D).elaborate.val :=
  RedundantSelectedTest.snd_discards X D

/-- Quoting the older of two slots gives the same selected terminal as the
direct read, provided the newest slot admits discard. -/
theorem second_quote {X : Ty Empty} {L : List (Ty Empty)}
    (pos : Position L) (slots : Fin 2 → Term signature.Instr X Bit) (bits : List Bool)
    (drop : Paper.Extension.ReturnDiscards Seed [X] (slots 0).elaborate.val) :
    selectedEq (selectTerminal pos (.read 1) slots bits)
      (selectTerminal pos (Finite.Expr.quote 2 (fun env => env 1)) slots bits) :=
  RedundantSelectedTest.second_quote pos slots bits drop

/-- The direct older-slot read and its full quote give equal packed singleton
arrows from the two-reply product to the same tagged exit interface. -/
theorem packed_second_quote {L : List (Ty Empty)} (pos : Position L) (bits : List Bool) :
    packed (.ret (n := 2) bits pos 1) = packed (.retExpr bits pos (Finite.Expr.quote 2 (fun env => env 1))) :=
  RedundantSelectedTest.packed_second_quote pos bits

/-- A full quote reduces at a tagged constructor packet to its selected
Boolean row at the original ordered position. -/
theorem quoted_replyPacket {Γ L : List (Ty Empty)} {n : Nat}
    (pos : Position L) (table : Finite.Table n) (order : Fin n → Fin n)
    (env : Finite.Assignment n) (payload : Fin n → Tm signature.Instr) {base : Tm signature.Instr}
    (hb : Tm.BranchValue Γ base unit) (hp : ∀ j, Tm.BranchValue Γ (payload j) unit) :
    E Γ ((selectTerminal pos (Finite.Expr.quote n table) (readReply n ∘ order) []).elaborate.val.substVars
      (Tm.singleSubst (replyPacket env payload base)))
      (.let₁ .unit (.br pos.1 (if table (env ∘ order) then .inr (.var 0) else .inl (.var 0)))) L :=
  RedundantSelectedTest.quoted_replyPacket pos table order env payload hb hp

/-- Constructor substitution of a tagged two-reply packet into a full
quote reduces to the literal row at the given ordered position. -/
theorem quoted_packet {Γ L : List (Ty Empty)} (pos : Position L) (table : Finite.Table 2)
    (order : Fin 2 → Fin 2) (older newer : Bool) {u x y : Tm signature.Instr}
    (hu : Tm.BranchValue Γ u unit) (hx : Tm.BranchValue Γ x unit) (hy : Tm.BranchValue Γ y unit) :
    E Γ ((selectTerminal pos (Finite.Expr.quote 2 table) (readReply 2 ∘ order) []).elaborate.val.substVars
      (Tm.singleSubst (.pair (.pair u (if older then .inr x else .inl x)) (if newer then .inr y else .inl y))))
      (.let₁ .unit (.br pos.1 (if table (Fin.cases newer (fun _ => older) ∘ order)
        then .inr (.var 0) else .inl (.var 0)))) L :=
  RedundantSelectedTest.quoted_packet pos table order older newer hu hx hy

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
