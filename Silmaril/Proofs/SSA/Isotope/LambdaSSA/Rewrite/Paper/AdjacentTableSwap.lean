module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.AdjacentSwap.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.PacketCases.Thms
import Mathlib.Data.Fin.Rev

/-! # Slot permutations from native packet case extensionality -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AdjacentSwap

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithCaseBind.OpenReplay

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

theorem selected_permute_quote {n : Nat} {L : List (Ty Empty)} (pos : Position L)
    (bits : List Bool) (table : Finite.Table n) (order : Equiv.Perm (Fin n)) :
    selectedEq (selectTerminal pos (Finite.Expr.quote n table) (readReply n) bits)
      (selectTerminal pos (Finite.Expr.quote n (fun row => table (row ∘ order.symm)))
        (readReply n ∘ order) bits) := by
  let reindexed := fun row : Finite.Assignment n => table (row ∘ order.symm)
  let left := selectTerminal pos (Finite.Expr.quote n table) (readReply n) []
  let right := selectTerminal pos (Finite.Expr.quote n reindexed) (readReply n ∘ order) []
  have bare : selectedEq left right := by
    apply packet_case_ext left.elaborate.property.hasType right.elaborate.property.hasType
    intro env
    have base := packetBase_typed (Γ := [replyContext n]) (i := 0) (n := n) rfl
    have payload (j : Fin n) := packetPayload_typed (Γ := [replyContext n]) n j
    have normal := quoted_replyPacket pos table id env (packetPayload n) base payload
    have reordered := quoted_replyPacket pos reindexed order env (packetPayload n) base payload
    have recover : (env ∘ order) ∘ order.symm = env := by
      funext j
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    dsimp only [reindexed] at reordered
    simp only [recover] at reordered
    exact normal.trans reordered.symm
  exact (terminal_prefix (Finite.Expr.quote n table) pos (readReply n) bits).trans
    ((prependEmits_congr bits bare).trans
      (terminal_prefix (Finite.Expr.quote n reindexed) pos (readReply n ∘ order) bits).symm)

theorem packed_permute_quote {n : Nat} {L : List (Ty Empty)} (pos : Position L)
    (bits : List Bool) (table : Finite.Table n) (order : Equiv.Perm (Fin n)) :
    packed (.retExpr bits pos (Finite.Expr.quote n table)) =
      packedTable pos bits (fun row => table (row ∘ order.symm)) order := by
  let l := selectTerminal pos (Finite.Expr.quote n table) (readReply n) bits
  let r := selectTerminal pos (Finite.Expr.quote n (fun row => table (row ∘ order.symm)))
    (readReply n ∘ order) bits
  apply (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
  exact (selected_permute_quote pos bits table order).lsubstPost l.elaborate.property r.elaborate.property
    (fun _ _ hi => (packExits_valueFamily _ L hi).hasType)

theorem selected_adjacent_swap {L : List (Ty Empty)} (pos : Position L) (bits : List Bool)
    (table : Finite.Table 2) :
    selectedEq (selectTerminal pos (Finite.Expr.quote 2 table) (readReply 2) bits)
      (selectTerminal pos (Finite.Expr.quote 2 (fun row => table (row ∘ Fin.rev)))
        (readReply 2 ∘ Fin.rev) bits) :=
  selected_permute_quote pos bits table Fin.revPerm

theorem packed_adjacent_swap {L : List (Ty Empty)} (pos : Position L) (bits : List Bool)
    (table : Finite.Table 2) :
    packed (.retExpr bits pos (Finite.Expr.quote 2 table)) =
      packedTable pos bits (fun row => table (row ∘ Fin.rev)) Fin.rev :=
  packed_permute_quote pos bits table Fin.revPerm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AdjacentSwap
