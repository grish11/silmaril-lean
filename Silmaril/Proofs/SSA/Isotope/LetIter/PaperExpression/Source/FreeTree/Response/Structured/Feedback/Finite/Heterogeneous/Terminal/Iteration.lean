module

public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Bind

@[expose] public section

open Silmaril.Isotope Silmaril.Isotope.LetIter.LocallyNameless

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs

variable {count : Nat} {F : Family count} {S B C : Code} {ε : Type}
  [HasEff (Opcode F) ε] {pe : ε}

local notation "Ops" => Opcode F
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "H" => HasType Ops Free
local notation "E" => AbortEquiv (Φ := Ops) pe Free

/-- Use a closed single-input body beneath an arbitrary unused context. -/
def widen (b : Tm Empty Ops 1) (n : Nat) : Tm Empty Ops (n + 1) :=
  b.rename (fun _ => 0)

omit [HasEff (Opcode F) ε] in
@[simp] theorem widen_zero (b : Tm Empty Ops 1) : widen b 0 = b := by
  refine (Tm.rename_congr (fun i => ?_) b).trans (Tm.rename_id b)
  exact (Fin.eq_zero i).symm

omit [HasEff (Opcode F) ε] in
@[simp] theorem widen_under (b : Tm Empty Ops 1) (n : Nat) :
    (widen b n).underBinder = widen b (n + 1) := by
  rw [Tm.underBinder, widen, Tm.rename_comp]
  rfl

omit [HasEff (Opcode F) ε] in
@[simp] theorem widen_subst (b : Tm Empty Ops 1) {n m : Nat} (σ : Fin n → Tm Empty Ops m) :
    (widen b n).bsubst (Tm.upSub σ) = widen b m := by
  rw [widen, Tm.bsubst_rename, widen, ← Tm.bsubst_bv_eq_rename]
  apply Tm.bsubst_congr
  intro _
  rfl

omit [HasEff (Opcode F) ε] in
theorem widen_typed {b : Tm Empty Ops 1} {A R : Ty Unit} (hb : H (.snoc .nil A) b R)
    {n : Nat} (β : BoundCtx (Ty Unit) n) : H (β.snoc A) (widen b n) R := by
  refine HasType.rename ⟨fun _ => 0, fun i => ?_⟩ hb
  rw [Fin.eq_zero i]
  rfl

def loopArm (b : Tm Empty Ops 1) (n : Nat) : Tm Empty Ops (n + 1) :=
  .iter (.bv 0) (widen b (n + 1))

def loopHandler (b : Tm Empty Ops 1) : Tm Empty Ops 1 :=
  .case (.bv 0) (.bv 0) (loopArm b 1)

def flattenHandler (Φ : Type) : Tm Empty Φ 1 :=
  .case (.bv 0) (.bv 0) (.inr (.bv 0))

omit [HasEff (Opcode F) ε] in
theorem loopHandler_typed {b : Tm Empty Ops 1} (hb : H (.snoc .nil S.ty) b (Code.sum C S).ty) :
    H (.snoc .nil (Code.sum C S).ty) (loopHandler b) C.ty :=
  .case .bv .bv (.iter .bv (widen_typed hb _))

omit [HasEff (Opcode F) ε] in
private theorem plug_case (a l r : Tm Empty Ops 1) (v : Tm Empty Ops 0) :
    plug (.case a l.underBinder r.underBinder) v = .case (plug a v) l r := by
  have drop (u : Tm Empty Ops 1) :
      u.underBinder.bsubst (Tm.upSub (fun _ : Fin 1 => v)) = u :=
    (Tm.let₁.inj (plug_bind a u v)).2
  simp only [plug, Tm.bsubst, drop]

theorem handler_left {h : Tm Empty Ops 1} {l r : Tm Empty Ops 1}
    (shape : h = .case (.bv 0) l.underBinder r.underBinder)
    (hl : H (.snoc .nil C.ty) l B.ty) (hr : H (.snoc .nil S.ty) r B.ty) (v : C.Value) :
    E .nil (plug h (nativeValue Ops (Code.sum C S) (.inl v))) (plug l (nativeValue Ops C v)) B.ty := by
  subst h
  rw [plug_case]
  change E .nil (.case (.inl (nativeValue Ops C v)) l r) _ _
  exact (Refinement.equiv (Equiv.caseBetaL (value_typed C v .nil) hl hr)).trans (bind_value hl v)

theorem handler_right {h : Tm Empty Ops 1} {l r : Tm Empty Ops 1}
    (shape : h = .case (.bv 0) l.underBinder r.underBinder)
    (hl : H (.snoc .nil C.ty) l B.ty) (hr : H (.snoc .nil S.ty) r B.ty) (v : S.Value) :
    E .nil (plug h (nativeValue Ops (Code.sum C S) (.inr v))) (plug r (nativeValue Ops S v)) B.ty := by
  subst h
  rw [plug_case]
  change E .nil (.case (.inr (nativeValue Ops S v)) l r) _ _
  exact (Refinement.equiv (Equiv.caseBetaR (value_typed S v .nil) hl hr)).trans (bind_value hr v)

omit [HasEff (Opcode F) ε] in
theorem loopArm_under (b : Tm Empty Ops 1) (n : Nat) :
    (loopArm b n).underBinder = loopArm b (n + 1) := by
  unfold loopArm Tm.underBinder widen
  simp only [Tm.rename, Tm.rename_comp]
  rfl

omit [HasEff (Opcode F) ε] in
theorem loopArm_plug (b : Tm Empty Ops 1) (v : Tm Empty Ops 0) :
    plug (loopArm b 0) v = .iter v b := by
  simp only [plug, loopArm, Tm.bsubst, widen_subst, widen_zero]

theorem unfold_closed {b : Tm Empty Ops 1} (hb : H (.snoc .nil S.ty) b (Code.sum C S).ty) (s : S.Value) :
    E .nil (.iter (nativeValue Ops S s) b)
      (.let₁ (plug b (nativeValue Ops S s)) (loopHandler b)) C.ty := by
  let v : Tm Empty Ops 0 := nativeValue Ops S s
  have hv : H .nil v S.ty := value_typed S s .nil
  have arm : H (.snoc .nil S.ty) (loopArm b 0) C.ty := .iter .bv (widen_typed hb _)
  have unfoldEq := Equiv.fixpoint (pureEff := pe) hv hb
  have bodyEq : b.underBinder.underBinder = widen b 2 := by
    conv_lhs => rw [← widen_zero b, widen_under, widen_under]
  rw [bodyEq] at unfoldEq
  have step : H (.snoc .nil S.ty) (.case b (.bv 0) (loopArm b 1)) C.ty :=
    .case hb .bv (.iter .bv (widen_typed hb _))
  have beta := Equiv.letBeta (pureEff := pe) (value_pure S s 0) hv step
  rw [← plug_eq_instantiate] at beta
  have opened : plug (.case b (.bv 0) (loopArm b 1)) v =
      .case (plug b v) (.bv 0) (loopArm b 0) := by
    simp only [plug, loopArm, Tm.bsubst, Tm.upSub, Fin.cases_zero]
    rw [widen_subst]
  rw [opened] at beta
  have bind := Equiv.bindCase (pureEff := pe) (plug_typed hb hv)
    (show H (.snoc .nil C.ty) (.bv 0) C.ty from .bv) arm
  rw [loopArm_under] at bind
  exact .equiv (unfoldEq.trans (beta.trans bind))

theorem loopHandler_left {b : Tm Empty Ops 1} (hb : H (.snoc .nil S.ty) b (Code.sum C S).ty)
    (v : C.Value) :
    E .nil (plug (loopHandler b) (nativeValue Ops (Code.sum C S) (.inl v))) (nativeValue Ops C v) C.ty := by
  refine handler_left (l := .bv 0) (r := loopArm b 0) ?_ .bv (.iter .bv (widen_typed hb _)) v
  rw [loopArm_under]
  rfl

theorem loopHandler_right {b : Tm Empty Ops 1} (hb : H (.snoc .nil S.ty) b (Code.sum C S).ty)
    (v : S.Value) :
    E .nil (plug (loopHandler b) (nativeValue Ops (Code.sum C S) (.inr v)))
      (.iter (nativeValue Ops S v) b) C.ty := by
  rw [← loopArm_plug]
  refine handler_right (l := .bv 0) (r := loopArm b 0) ?_ .bv (.iter .bv (widen_typed hb _)) v
  rw [loopArm_under]
  rfl

theorem loop_return (M : Table F S C) (s : S.Value) {v : C.Value} (row : M s = .ret v) :
    E .nil (.iter (nativeValue Ops S s) (nativeBody M)) (nativeValue Ops C v) C.ty := by
  have step := body_beta (pe := pe) M s
  rw [row] at step
  have h := loopHandler_typed (body_typed M)
  exact (unfold_closed (body_typed M) s).trans ((Refinement.let₁ step (.refl h)).trans
    ((bind_value h (.inl v)).trans (loopHandler_left (body_typed M) v)))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.TerminalProofs
