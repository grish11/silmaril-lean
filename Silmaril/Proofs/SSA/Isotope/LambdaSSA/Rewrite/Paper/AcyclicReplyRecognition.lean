module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Thms

/-! # Native soundness of recognition for a case-entry block table -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AcyclicReplyRecognition

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies (Atom Profile ReplyShape)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic (Control)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition

variable {Φ : Type} [Profile Φ]

theorem call_region (op : Φ) {t : ReplyShape} (body : Control Φ (Profile.reply op) t) :
    (Control.let₁ (.call op) body).region =
      .let₁ (.op op (.var 0)) (body.region.renameVars (lift Nat.succ)) := by
  simp only [Control.region, compLSubst, CfgEta.TypeCategory.returnRegion, lsubst, liftLSubstVars]
  rw [substVars_renameVars]
  have tail : Tm.singleSubst (.var 0 : Tm Φ) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  rw [tail, substVars_var]

variable [DecidableEq Φ]

omit [Profile Φ] in
theorem sameBody_eq {a b : Region Φ} (h : sameBody a b = true) : a = b := by
  induction a generalizing b <;> cases b <;> simp_all [sameBody, Bool.and_eq_true]
  all_goals aesop

private theorem arm_sound {s t : ReplyShape} {ρ : Nat → Nat} {raw : Region Φ}
    {p : Control Φ s t} (h : recognizeArm s t ρ raw = some p) :
    raw = arm ρ p := by
  unfold recognizeArm at h
  obtain ⟨q, _, hq⟩ := Option.bind_eq_some_iff.mp h
  split at hq
  · rename_i matched
    exact (sameBody_eq matched).trans (congrArg (arm ρ) (Option.some.inj hq))
  · cases hq

omit [DecidableEq Φ] in
private theorem case_table {Γ : VCtx (Ty Atom)} {l r t : ReplyShape}
    (ρ : Nat → Nat) (w : SSA.Ren [(ReplyShape.sum l r).ty] Γ ρ)
    (left : Control Φ l t) (right : Control Φ r t) :
    Paper.Eqv Γ (.cfg (caseEntry (ρ 0)) 2 (Fin.cases (arm ρ left) (fun _ => arm ρ right)))
      ((Control.case left right).region.renameVars ρ) [t.ty] := by
  let lhs := (left.region.renameVars (lift Nat.succ)).renameVars (lift ρ)
  let rhs := (right.region.renameVars (lift Nat.succ)).renameVars (lift ρ)
  have cfg : (.cfg (caseEntry (ρ 0)) 2 (Fin.cases (arm ρ left) (fun _ => arm ρ right))) =
      Region.caseCfg (.var (ρ 0)) lhs rhs := by
    unfold Region.caseCfg caseEntry
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [cfg]
  have h := (Control.case left right).region_typed.renameVars w
  change ValueBranches Γ (.case (.var (ρ 0)) lhs rhs) [t.ty] at h
  cases h with
  | case ha hl hr =>
      exact (Paper.Eqv.cfgEta (.native (.caseCfg ha hl.hasType hr.hasType))).symm

theorem table_sound {Γ : VCtx (Ty Atom)} {s t : ReplyShape} {ρ : Nat → Nat}
    (w : SSA.Ren [s.ty] Γ ρ) {raw : Region Φ} {p : Control Φ s t}
    (accepted : recognizeTable s t ρ raw = some p) :
    Paper.Eqv Γ raw (p.region.renameVars ρ) [t.ty] := by
  cases s with
  | empty => simp [recognizeTable] at accepted
  | unit => simp [recognizeTable] at accepted
  | sum l r =>
      cases raw <;> try (change none = some p at accepted; cases accepted)
      case cfg entry n blocks =>
        rcases n with _ | _ | _ | n <;> try (change none = some p at accepted; cases accepted)
        change (if sameBody entry (caseEntry (ρ 0)) then
          do
            let left ← recognizeArm l t ρ (blocks 0)
            let right ← recognizeArm r t ρ (blocks 1)
            some (.case left right)
          else none) = some p at accepted
        split at accepted
        · rename_i matched
          obtain ⟨left, hleft, tail⟩ := Option.bind_eq_some_iff.mp accepted
          obtain ⟨right, hright, hp⟩ := Option.bind_eq_some_iff.mp tail
          have ep : Control.case left right = p := Option.some.inj hp
          subst p
          have table : blocks = Fin.cases (arm ρ left) (fun _ => arm ρ right) := by
            funext i
            refine Fin.cases (arm_sound hleft) (fun j => ?_) i
            have hj : j = 0 := Fin.eq_zero j
            subst j
            exact arm_sound hright
          rw [sameBody_eq matched, table]
          exact case_table ρ w left right
        · cases accepted

theorem sound {t : ReplyShape} {r : Region Φ} {p : Control Φ .unit t}
    (accepted : recognize t r = some p) :
    Paper.Eqv [(ReplyShape.unit).ty] r p.region [t.ty] := by
  cases r <;> try (change none = some p at accepted; cases accepted)
  case let₁ a body =>
    cases a <;> try (change none = some p at accepted; cases accepted)
    case op op arg =>
      cases arg <;> try (change none = some p at accepted; cases accepted)
      case var i =>
        cases i <;> try (change none = some p at accepted; cases accepted)
        change Option.map (.let₁ (.call op))
          (recognizeTable (Profile.reply op) t (lift Nat.succ) body) = some p at accepted
        obtain ⟨q, hq, hp⟩ := Option.map_eq_some_iff.mp accepted
        subst p
        rw [call_region]
        exact .let₁ (.op (.var rfl)) (table_sound
          ((SSA.Ren.wk [] (ReplyShape.unit).ty).lift (Profile.reply op).ty) hq)

open Example

theorem graph_typed {i : Nat} {right : Region Op}
    (hi : At [ReplyShape.unit.ty, Reply.ty, ReplyShape.unit.ty] i ReplyShape.unit.ty)
    (hr : ValueBranches [ReplyShape.unit.ty, Reply.ty, ReplyShape.unit.ty] right
      [ReplyShape.unit.ty, ReplyShape.unit.ty, Reply.ty]) :
    ValueBranches [ReplyShape.unit.ty] (graph i right) [Reply.ty] := by
  apply ValueBranches.let₁ (.op (.var rfl))
  refine .cfg (fun _ : Fin 2 => ReplyShape.unit.ty) ?_ ?_
  · exact .case (.var rfl) (.br rfl (.var rfl)) (.br rfl (.var rfl))
  · intro j
    refine Fin.cases ?_ (fun _ => ?_) j
    · exact .br rfl (.inl (.var hi))
    · exact hr

theorem return_right_typed :
    ValueBranches [ReplyShape.unit.ty, Reply.ty, ReplyShape.unit.ty] returnRight
      [ReplyShape.unit.ty, ReplyShape.unit.ty, Reply.ty] :=
  .let₁ (.op (.var rfl)) (.br rfl (.inr (.var rfl)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AcyclicReplyRecognition
