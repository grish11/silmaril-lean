module

public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Dispatch

public section

open Silmaril.Isotope Silmaril.Isotope.LetIter.LocallyNameless

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs

variable {n : Nat} {F : Family n} {S B C : Code} {ε : Type} [HasEff (Opcode F) ε] {pe : ε}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "H" => HasType Ops Free
local notation "E" => AbortEquiv (Φ := Ops) pe Free

omit [HasEff (Opcode F) ε] in
theorem plug_bind (a h : Tm Empty Ops 1) (v : Tm Empty Ops 0) :
    plug (.let₁ a h.underBinder) v = .let₁ (plug a v) h := by
  have move : h.underBinder.bsubst (Tm.upSub (fun _ : Fin 1 => v)) = h := by
    rw [Tm.underBinder, Tm.bsubst_rename]
    refine (Tm.bsubst_congr (fun i => ?_) h).trans ((Tm.bsubst_bv_eq_rename id h).trans (Tm.rename_id h))
    rw [Fin.eq_zero i]
    rfl
  exact congrArg (Tm.let₁ (plug a v)) move

theorem bind_value {h : Tm Empty Ops 1} {A : Ty Unit}
    (ht : H (.snoc .nil C.ty) h A) (v : C.Value) :
    E .nil (.let₁ (nativeValue Ops C v) h) (plug h (nativeValue Ops C v)) A := by
  rw [plug_eq_instantiate]
  exact .equiv (Equiv.letBeta (value_pure C v 0) (value_typed C v .nil) ht)

/-- Postcompose a rendered call by a native handler. A typed proof at each
constructor reply rewrites the whole continuation. -/
theorem bind_call {f : Ops} (x : f.argCode.Value)
    (k : f.replyCode.Value → B.Value ⊕ S.Value) (next : f.replyCode.Value → C.Value ⊕ S.Value)
    {h : Tm Empty Ops 1} (ht : H (.snoc .nil (Code.sum B S).ty) h (Code.sum C S).ty)
    (eq : ∀ r, E .nil (plug h (nativeValue Ops (Code.sum B S) (k r)))
      (nativeValue Ops (Code.sum C S) (next r)) (Code.sum C S).ty) :
    E .nil (.let₁ (nativeRow (.call f x k) 0) h) (nativeRow (.call f x next) 0) (Code.sum C S).ty := by
  have req : H .nil (.op f (nativeValue Ops f.argCode x)) f.replyCode.ty :=
    .op (value_typed f.argCode x .nil)
  have lhs := reply_typed k (show H (.snoc .nil f.replyCode.ty) (.bv 0) f.replyCode.ty from .bv)
  have rhs := reply_typed next (show H (.snoc .nil f.replyCode.ty) (.bv 0) f.replyCode.ty from .bv)
  have cont := by_values f.replyCode (.let₁ lhs ht.underBinder) rhs (fun r => by
    rw [plug_bind]
    simp only [plug, reply_subst, Tm.bsubst] at ⊢
    have same := eq r
    exact (Refinement.let₁ (reply_beta k r) (.refl ht)).trans
      ((bind_value ht (k r)).trans (same.trans (reply_beta next r).symm)))
  exact (Refinement.equiv (Equiv.bindLet req lhs ht)).trans (.let₁ (.refl req) cont)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs
