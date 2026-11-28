module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Defs

/-! # Native emit prefixes for the selected reply tables -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

/-- Emit in order, then enter the original region with its input retained. -/
def prependEmits : List Bool → Region signature.Instr → Region signature.Instr
  | [], r => r
  | b :: bs, r => .let₁ (.op (show signature.Instr from Op.emit b) .unit)
      ((prependEmits bs r).renameVars Nat.succ)

open Silmaril
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithComputedProductProducers.Intrinsic (Term)

local instance priorCaseUnitHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Read the prior case's unit payload through the intervening reply field. -/
def priorCaseUnit (X : Ty Empty) :
    Term signature.Instr (product (product X unit) Bit) unit :=
  .seq (.fst (product X unit) Bit) (.snd X unit)

/-- The native equation for a single return after substituting its input packet. -/
abbrev ReturnsAt {Γ : List (Ty Empty)} {X D : Ty Empty} (t : Term signature.Instr X D)
    (packet result : Tm signature.Instr) : Prop :=
  Paper.Extension.Eqv Seed Γ (Paper.RetainedLet.returnOnce (t.elaborate.val.subst (Tm.singleSubst packet)))
    (.br 0 result) [D]

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
