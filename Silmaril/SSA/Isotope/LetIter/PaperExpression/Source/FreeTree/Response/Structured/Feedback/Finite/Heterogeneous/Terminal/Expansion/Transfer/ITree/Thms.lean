module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Transfer.Thms

/-! # Weak ITree soundness of the actual transfer-plan expansion -/

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S B : Code} {ε : Type} [HasEff (Opcode F) ε] [Bot ε]
  {Events : Type → Type}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "D" => Ty.denote (Lifted carriers)

/-- Both actual lowerings have the same weak observation in a shared
instruction interpretation that interprets bottom-effect primitives purely. -/
theorem TransferPlans.denote_expand_eq (M : TransferPlans F S B) (s : S.Value)
    (instr : InstructionModel D Ops (ITree.Tree Events))
    (pureInstr : InstructionModel.RespectsPure (ε := ε) instr)
    {a a' : Tm Empty Ops 0} {b b' : Tm Empty Ops 1}
    (ha : (S.literal s).toLetIter 0 = some a) (hb : M.source.toLetIter 1 = some b)
    (ha' : (M.stateCode.literal (.inl s)).toLetIter 0 = some a')
    (hb' : M.expand.source.toLetIter 1 = some b')
    (d : Derivation Ops Free .nil (.iter a b) B.ty)
    (d' : Derivation Ops Free .nil (.iter a' b') B.ty) :
    d.denote D instr (fun x => x.elim) (fun i => i.elim0) =
      d'.denote D instr (fun x => x.elim) (fun i => i.elim0) :=
  LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil (Lifted carriers) instr pureInstr
    (M.expand_eq (pe := (⊥ : ε)) s ha hb ha' hb') d d' (fun i => i.elim0)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous
