module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs

/-! # Packing a selected table with an explicit slot order -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance adjacentSwapDefsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Pack the actual selected table at its original reply product. The order
indexes the packet projections and the quote consumes those slots in order. -/
def packedTable {n : Nat} {L : List (Ty Empty)} (pos : Position L) (bits : List Bool)
    (table : Finite.Table n) (order : Fin n → Fin n) :
    Paper.Extension.Singleton.ofType Seed (replyContext n) ⟶
      Paper.Extension.Singleton.ofType Seed (packedExitType L) :=
  Paper.Extension.Singleton.ofRegion Seed
    (selectTerminal pos (Finite.Expr.quote n table) (readReply n ∘ order) bits).elaborate.property.packExits

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
