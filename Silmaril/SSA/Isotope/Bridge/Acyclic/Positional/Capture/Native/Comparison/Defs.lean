module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
public import Silmaril.SSA.Isotope.LetCase.Thms

/-! # Comparison at the actual packed CFG endpoints -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {d n : Nat} {β : BoundCtx τ d} {L : LCtx τ}

/-- Evaluate each branch operand once before tagging its original outward
position. Local labels retain their original meaning. -/
abbrev Table.packedSSA (p : Table Φ β L n) (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :=
  (p.toSSA i a).bindBranchArguments.packExits

theorem Table.packedSSA_hasType (p : Table Φ β L n) (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    Region.HasType β.toList (p.packedSSA i a) [Region.packedExitType L] :=
  (p.toSSA_hasType i a).bindBranchArguments.hasType.packExits

open LetCase.LocallyNameless (HasType Pure)
local notation "Term" => LetCase.LocallyNameless.Tm Empty
open Region.Paper.RetainedLet (returnOnce)
open Morphism.CaseSSA (erase)

/-- The root obligation for general signatures is substitution of a pure LetCase expression
whose erasure is not an SSA branch value. The endpoint types and the literal
substitution are those of native LetCase let β. -/
def PureLetBetaReplay {α : Type u} {Ψ : Type v} [HasTy Ψ (Ty α)] {ε : Type w} [HasEff Ψ ε]
    (pe : ε) : Prop :=
  ∀ {n : Nat} {β : BoundCtx (Ty α) n} {a : Term Ψ n} {b : Term Ψ (n + 1)} {A B : Ty α},
    Pure pe a →
    HasType Ψ (.nil : Ctx Empty (Ty α)) β a A →
    HasType Ψ (.nil : Ctx Empty (Ty α)) (β.snoc A) b B →
    ¬ Tm.BranchValue β.toList (erase a) A →
    ReplayEqv pe β.toList (returnOnce (erase (.let₁ a b))) (returnOnce (erase (b.instantiate a))) [B]

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
