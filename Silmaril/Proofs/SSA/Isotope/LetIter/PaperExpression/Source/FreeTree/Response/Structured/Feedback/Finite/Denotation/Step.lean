module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Denotation.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Thms

import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
import Silmaril.SSA.Isotope.LetIter.Monadic.Substitution.Thms

public section

open Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation DerivSubst)
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.DenotationProofs

section ConstructorSemantics

variable {Ops : Type} [HasTy Ops (Ty Unit)] {ε : Type} [HasEff Ops ε]
  [SemilatticeSup ε] [OrderBot ε] {e : ε}

local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "Den" => Ty.denote (Lifted carriers)
local notation "Events" => Event (Φ := Ops) carriers
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def shape : (c : Code) → c.Value → ReplyShape (Fin.elim0 : Fin 0 → Unit) c.ty
  | .unit, _ => .unit
  | .sum l _, .inl v => .inl (shape l v)
  | .sum _ r, .inr v => .inr (shape r v)

omit [HasTy Ops (Ty Unit)] in
private theorem shape_source (c : Code) (v : c.Value) {n : Nat} (p : Fin 0 → Fin n) :
    (shape c v).source (Φ := Ops) p = c.literal v := by
  induction c with
  | unit => rfl
  | sum l r il ir =>
      cases v with
      | inl x => exact congrArg Expr.inl (il x)
      | inr x => exact congrArg Expr.inr (ir x)

private theorem shape_value (c : Code) (v : c.Value) (values : (i : Fin 0) → Den (.base (i.elim0 : Unit))) :
    (shape c v).denote (Lifted carriers) values = c.raise v := by
  induction c with
  | unit => rfl
  | sum l r il ir =>
      cases v with
      | inl x => exact congrArg Sum.inl (il x)
      | inr x => exact congrArg Sum.inr (ir x)

/-- Every closed table literal has the indicated constructor value in any
ambient bound environment. -/
theorem literal_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers) (c : Code) (v : c.Value)
    {n : Nat} {β : BoundCtx (Ty Unit) n} (ρ : BoundEnv Den β) :
    ∃ (t : Tm Empty Ops n) (d : Derivation Ops Free β t c.ty),
      (c.literal v).toLetIter n = some t ∧ d.denote Den (instructions carriers P) γ ρ = pure (c.raise v) := by
  let sh := shape c v
  let p : Fin 0 → Fin n := Fin.elim0
  let typed : ∀ i, β.get (p i) = .base ((Fin.elim0 : Fin 0 → Unit) i) := fun i => i.elim0
  let vals : (i : Fin 0) → Lifted carriers ((Fin.elim0 : Fin 0 → Unit) i) := fun i => i.elim0
  refine ⟨sh.native p, sh.derivation p typed, ?_, ?_⟩
  · rw [← shape_source (Ops := Ops) c v p]
    exact sh.lowers p
  · have h := sh.denote_derivation p (Lifted carriers) (instructions carriers P) typed ρ vals
        (fun i => i.elim0)
    rw [shape_value] at h
    exact h

variable [EffectIteration ε] in
theorem specialize_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    {c : Code} (v : c.Value) {a rhs : Expr Ops} {A : Ty Unit}
    {t : Tm Empty Ops 1} {r : Tm Empty Ops 0}
    (d : Derivation Ops Free (.snoc .nil c.ty) t A) (dr : Derivation Ops Free .nil r A)
    (hl : a.toLetIter 1 = some t) (hr : rhs.toLetIter 0 = some r)
    (eq : Eqv ([] : EffectCtx (Ty Unit) ε) A e (a.subst (c.literal v).subst0) rhs) :
    d.denote Den (instructions carriers P) γ (BoundEnv.snoc ρ₀ (c.raise v)) =
      dr.denote Den (instructions carriers P) γ ρ₀ := by
  obtain ⟨lit, dlit, hLit, hValue⟩ := literal_denote P c v (β := .nil) ρ₀
  let σ : Fin 1 → Tm Empty Ops 0 := fun _ => lit
  let ds : DerivSubst (Γ := Free) (.snoc .nil c.ty) .nil σ :=
    Fin.cases dlit (fun i => i.elim0)
  have lowered := Expr.toLetIter_subst (σ := (c.literal v : Expr Ops).subst0) (θ := σ) hl
    (fun i => Fin.cases hLit (fun j => j.elim0) i)
  have soundEq := sound carriers P (eq.toLetIter lowered hr) (d.bsubst ds) dr ρ₀
  have values (i : Fin 1) : (ds i).denote Den (instructions carriers P) γ ρ₀ =
      pure (BoundEnv.snoc (D := Den) ρ₀ (c.raise v) i) := by
    rw [Fin.eq_zero i]
    exact hValue
  exact (Derivation.denote_bsubst Den (instructions carriers P) γ d ds _ ρ₀ values).symm.trans soundEq

end ConstructorSemantics

variable {Q K S B : Code} {ε : Type} [HasEff (Opcode Q K) ε] [SemilatticeSup ε] [OrderBot ε]
  [EffectIteration ε] {e : ε}

local notation "Ops" => Opcode Q K
local notation "Free" => (Ctx.nil : Ctx Empty (Ty Unit))
local notation "Den" => Ty.denote (Lifted carriers)
local notation "Events" => Event (Φ := Ops) carriers
local notation "γ" => (fun x : Empty => x.elim)
local notation "ρ₀" => (fun i : Fin 0 => i.elim0)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev responseBody (M : Table Q K S B) (s : S.Value) : Expr Ops :=
  K.dispatch (fun r => (Code.sum B S).literal (M.reply s r)) (.var 0)

omit [EffectIteration ε] in
private theorem response_wf (M : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e) :
    Wf [(K.ty, ⊥)] (responseBody M s) (Code.sum B S).ty e := by
  have typed := (M.step_readback s hf).endpoints_wf.2
  change Wf ([] : EffectCtx (Ty Unit) ε) (.let₁ (.op .ask (Q.literal (M.request s))) (responseBody M s))
    (Code.sum B S).ty e at typed
  cases typed with
  | let₁ req next =>
      cases req
      exact next

/-- The rendered body performs one visible request, then returns the
encoded control result specified by its row and the supplied reply. -/
theorem step_denote (P : PureMaps (Φ := Ops) (ε := ε) carriers)
    (visible : ¬ IsPure (⊥ : ε) (Opcode.ask : Ops))
    (M : Table Q K S B) (s : S.Value) (hf : instrEff (Opcode.ask : Ops) ≤ e)
    {t : Tm Empty Ops 1} (hl : M.source.toLetIter 1 = some t)
    (d : Derivation Ops Free (.snoc .nil S.ty) t (Code.sum B S).ty) :
    d.denote Den (instructions carriers P) γ (BoundEnv.snoc ρ₀ (S.raise s)) =
      ITree.vis (.call (Opcode.ask : Ops) (M.request s)) (fun r => ITree.ret ((Code.sum B S).raise (M.reply s r))) := by
  obtain ⟨x, dx, lx, hx⟩ := literal_denote P Q (M.request s) (β := .nil) ρ₀
  obtain ⟨k, lk, hk⟩ := (response_wf M s hf).toLetIter
  obtain ⟨dk⟩ := Derivation.ofHasType hk.1
  change (responseBody M s).toLetIter 1 = some k at lk
  have rowLower : (M.row s).toLetIter 0 = some (.let₁ (.op .ask x) k) := by
    unfold Table.row
    change (Expr.let₁ (.op .ask (Q.literal (M.request s))) (responseBody M s)).toLetIter 0 = _
    simp [Expr.toLetIter, lx, lk]
  rw [specialize_denote P s d (.let₁ (.op dx) dk) hl rowLower (M.step_readback s hf)]
  rw [denote_letOp_of_not_pure carriers P visible dx dk ρ₀, hx, pure_bind]
  have argument : toSmall carriers (instrSrc (Opcode.ask : Ops)) (Q.raise (M.request s)) = M.request s :=
    (toSmall carriers Q.ty).apply_symm_apply _
  rw [argument]
  congr 1
  funext r
  obtain ⟨val, dv, lv, hv⟩ := literal_denote P (Code.sum B S) (M.reply s r) (β := .nil) ρ₀
  exact (specialize_denote P r dk dv lk lv (M.reply_readback s r (e := e))).trans hv

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.DenotationProofs
