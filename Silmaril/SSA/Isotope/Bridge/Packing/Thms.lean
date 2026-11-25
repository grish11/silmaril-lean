module

public import Silmaril.SSA.Isotope.Bridge.Thms
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms

/-! # Packing native LetIter terms into the λiter syntactic category -/

public section

universe u

namespace Silmaril.Isotope.Bridge

open Silmaril.Thesis.LambdaIter
open Silmaril.Thesis.LambdaIter.Syn.SynCat

variable {S : Sig.{u}}
  [Silmaril.TypeFormers S.Ty] [Silmaril.HasTy S.Instr S.Ty] [Silmaril.HasEff S.Instr S.Eff]

/-- Under compatibility of the signatures, equality of the packed arrows reflects
and preserves the native exact LetIter equations in any bound context. -/
theorem packedArrow_eq_iff_equiv (hT : TypeCompat S.Ty)
    (hI : InstrCompat S.Instr S.Ty) (hE : EffCompat S.Instr S.Eff)
    {n : Nat} {β : Silmaril.Isotope.BoundCtx S.Ty n} {A : S.Ty}
    {t v : Silmaril.Isotope.LetIter.LocallyNameless.Tm Empty S.Instr n}
    (h : LocallyNameless.HasType S.Instr .nil (BoundCtx.toThesis β) (toThesis t) A)
    (k : LocallyNameless.HasType S.Instr .nil (BoundCtx.toThesis β) (toThesis v) A) :
    packedArrow (S := S) h = packedArrow k ↔
      Silmaril.Isotope.LetIter.LocallyNameless.Equiv S.pureEff .nil β t v A :=
  (packedArrow_eq_iff h k).trans (equiv_iff hT hI hE S.pureEff (Γ := .nil) (β := β) (a := t) (b := v)).symm

end Silmaril.Isotope.Bridge
