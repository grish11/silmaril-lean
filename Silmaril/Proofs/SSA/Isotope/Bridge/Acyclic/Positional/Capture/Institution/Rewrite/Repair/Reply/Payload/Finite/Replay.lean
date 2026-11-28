module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite

open Isotope.LetCase.LocallyNameless (Equiv HasType Tm)
open LambdaSSA.Region (packedExitType)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)
local notation "Term" => Tm Empty signature.Instr

theorem assignment_eta_proof {n : Nat} (env : Assignment (n + 1)) :
    env.tail.push (env 0) = env := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem quote_eval_proof (n : Nat) (table : Table n) (env : Assignment n) :
    (Expr.quote n table).eval env = table env := by
  induction n with
  | zero =>
    change table Fin.elim0 = table env
    congr 1
    funext i
    exact i.elim0
  | succ n ih =>
    have eta := assignment_eta_proof env
    cases h : env 0
    · change (if env 0 then _ else _) = _
      rw [h, ite_eq_right Bool.false_ne_true, ih, ← h, eta]
    · change (if env 0 then _ else _) = _
      rw [h, ite_eq_left rfl, ih, ← h, eta]

private theorem instantiate_lift {k : Nat} (t a : Term k) :
    Tm.instantiate t.lift a = t := by
  unfold Tm.instantiate Tm.lift
  rw [Tm.bsubst_rename]
  exact Tm.bsubst_id t

private theorem underBinder_lift {k : Nat} (t : Term k) :
    t.lift.underBinder = t.lift.lift :=
  Tm.rename_lift Fin.succ t

/-- Splitting on a pure retained bit can introduce two identical weakened
branches. The equality uses typed substitution under the payload binder. -/
theorem ignore_case_proof {k : Nat} {β : BoundCtx Sorts k} {i : Fin k}
    {t : Term k} {A : Sorts}
    (read : HasType signature.Instr Γ₀ β (.bv i) Bit)
    (body : HasType signature.Instr Γ₀ β t A) :
    Equiv false Γ₀ β t (.case (.bv i) t.lift t.lift) A := by
  have continuation : HasType signature.Instr Γ₀ (β.snoc Bit) t.lift A := body.lift
  have forget : Equiv false Γ₀ β (.let₁ (.bv i) t.lift) t A := by
    simpa only [instantiate_lift] using Equiv.letBeta (pureEff := false) .bv read continuation
  have low : HasType signature.Instr Γ₀ (β.snoc U) (.inl (.bv 0)) Bit := .inl .bv
  have high : HasType signature.Instr Γ₀ (β.snoc U) (.inr (.bv 0)) Bit := .inr .bv
  have eta := Equiv.let₁ (Equiv.caseEta (pureEff := false) read).symm (.refl continuation)
  have distribute := Equiv.bindLetCase (pureEff := false) read low high continuation
  have reduceLow : Equiv false Γ₀ (β.snoc U) (.let₁ (.inl (.bv 0)) t.lift.underBinder) t.lift A := by
    have reduce := Equiv.letBeta (pureEff := false) (.inl .bv) low continuation.underBinder
    rw [underBinder_lift, instantiate_lift] at reduce
    rw [underBinder_lift]
    exact reduce
  have reduceHigh : Equiv false Γ₀ (β.snoc U) (.let₁ (.inr (.bv 0)) t.lift.underBinder) t.lift A := by
    have reduce := Equiv.letBeta (pureEff := false) (.inr .bv) high continuation.underBinder
    rw [underBinder_lift, instantiate_lift] at reduce
    rw [underBinder_lift]
    exact reduce
  exact forget.symm.trans (eta.trans (distribute.trans (.case (.refl read) reduceLow reduceHigh)))

private theorem literal_replay (n : Nat) (b : Bool) {k : Nat} {β : BoundCtx Sorts k}
    (slots : Retained β n) :
    Equiv false Γ₀ β (bitOperand β b).1
      ((Expr.quote n (fun _ => b)).operand slots).1 Bit := by
  induction n generalizing k with
  | zero => exact .refl (bitOperand β b).2.toHasType
  | succ n ih =>
    let d := (slots.read 0).2.toHasType
    let older : Retained (β.snoc U) n := fun i => slots.weaken U i.succ
    have introduce := ignore_case_proof d (bitOperand β b).2.toHasType
    have lift : (bitOperand β b).1.lift = (bitOperand (β.snoc U) b).1 := by cases b <;> rfl
    rw [lift] at introduce
    exact introduce.trans (.case (.refl d) (ih older) (ih older))

private theorem read_replay (n : Nat) (i : Fin n) {k : Nat} {β : BoundCtx Sorts k}
    (slots : Retained β n) :
    Equiv false Γ₀ β (slots.read i).1 ((Expr.quote n (fun env => env i)).operand slots).1 Bit := by
  induction n generalizing k with
  | zero => exact i.elim0
  | succ n ih =>
    let d := (slots.read 0).2.toHasType
    let older : Retained (β.snoc U) n := fun j => slots.weaken U j.succ
    refine Fin.cases ?_ (fun j => ?_) i
    · have expand := Payload.Expr.replay .payload β (slots 0).1 (slots 0).2
      exact expand.trans (.case (.refl d) (literal_replay n false older) (literal_replay n true older))
    · have expand := ignore_case_proof d (slots.read j.succ).2.toHasType
      exact expand.trans (.case (.refl d) (ih j older) (ih j older))

theorem expr_replay_proof {n : Nat} (e : Expr n) {k : Nat} {β : BoundCtx Sorts k}
    (slots : Retained β n) :
    Equiv false Γ₀ β (e.operand slots).1 ((Expr.quote n e.eval).operand slots).1 Bit := by
  induction e generalizing k with
  | literal b => exact literal_replay _ b slots
  | read i => exact read_replay _ i slots
  | split l r ihl ihr =>
    let older : Retained (β.snoc U) _ := fun i => slots.weaken U i.succ
    exact .case (.refl (slots.read 0).2.toHasType) (ihl older) (ihr older)

theorem tree_replay_proof {L : List Sorts} {n : Nat} (p : Tree L n)
    {k : Nat} {β : BoundCtx Sorts k} (slots : Retained β n) :
    Equiv false Γ₀ β (p.operand slots).1 (p.normal.render.operand slots).1 (packedExitType L) := by
  induction p generalizing k with
  | ret p e => exact tag_congr L _ p.typed _ _ (expr_replay_proof e slots)
  | emit _ _ ih => exact .let₁ (.refl (.op .unit)) (ih (slots.weaken U))
  | request req bound _ _ ihl ihr =>
    exact request_replay req bound _ _ _ _ (ihl slots.bind) (ihr slots.bind)
  | testRequest test low lowBound highBound _ _ _ _ ihll ihlr ihhl ihhr =>
    let scope := ((slots.without test).weaken U).bind
    exact .case (.refl (slots.read test).2.toHasType)
      (request_replay low lowBound _ _ _ _ (ihll scope) (ihlr scope))
      (request_replay (!low) highBound _ _ _ _ (ihhl scope) (ihhr scope))

theorem derive_normal_proof (H : Sorts) (L : List Sorts) (p q : Tree (H :: L) 0)
    (h : p.normal = q.normal) : Derivable false (equation H L p q) := by
  have replay := tree_replay_proof p (β := .nil) Fin.elim0
  rw [h] at replay
  exact .let₁ (replay.trans (tree_replay_proof q Fin.elim0).symm)
    (.refl ((program H L p).body.render .base).encode.toLetCase.2.toHasType)

theorem derive_render_proof (H : Sorts) (L : List Sorts) (p : Tree (H :: L) 0) :
    Derivable false (equation H L p p.normal.render) :=
  .let₁ (tree_replay_proof p Fin.elim0)
    (.refl ((program H L p).body.render .base).encode.toLetCase.2.toHasType)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite
