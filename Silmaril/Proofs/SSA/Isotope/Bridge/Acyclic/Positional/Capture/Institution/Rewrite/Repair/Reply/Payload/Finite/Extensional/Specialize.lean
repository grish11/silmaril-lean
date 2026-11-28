module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.CommonRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Extensional.Cover

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional

open Isotope.LetCase.LocallyNameless (Equiv HasType PureTypedSubst Tm)
open LambdaSSA (At)
open LambdaSSA.Acyclic (FiniteExit Operand)
open LambdaSSA.Region (packedExitType)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)
local notation "Term" => Tm Empty signature.Instr

private theorem tag_subst {k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    (L : List Sorts) (i : Nat) {A : Sorts} (h : At L i A)
    (a : Operand signature.Instr β A) (b : Operand signature.Instr γ A) (σ : Fin k → Term m)
    (e : a.1.bsubst σ = b.1) :
    (FiniteExit.tag L i h a).1.bsubst σ = (FiniteExit.tag L i h b).1 := by
  induction L generalizing i with
  | nil => cases i <;> contradiction
  | cons T L ih =>
    cases i with
    | zero =>
      have ht : T = A := Option.some.inj h
      cases ht
      exact congrArg Tm.inl e
    | succ i => exact congrArg Tm.inr (ih i h)

private theorem tag_subst_equiv {k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    (L : List Sorts) (i : Nat) {A : Sorts} (h : At L i A)
    (a : Operand signature.Instr β A) (b : Operand signature.Instr γ A) (σ : Fin k → Term m)
    (e : Equiv false Γ₀ γ (a.1.bsubst σ) b.1 A) :
    Equiv false Γ₀ γ ((FiniteExit.tag L i h a).1.bsubst σ) (FiniteExit.tag L i h b).1 (packedExitType L) := by
  induction L generalizing i with
  | nil => cases i <;> contradiction
  | cons T L ih =>
    cases i with
    | zero =>
      have ht : T = A := Option.some.inj h
      cases ht
      exact .inl e
    | succ i => exact .inr (ih i h)

private theorem path_subst {L : List Sorts} (p : Path L) {k m : Nat}
    (β : BoundCtx Sorts k) (γ : BoundCtx Sorts m) (σ : Fin k → Term m) :
    (p.operand β).1.bsubst σ = (p.operand γ).1 := by
  induction p generalizing k m with
  | ret pos b => exact tag_subst L _ pos.typed _ _ σ (literal_bsubst β γ σ b)
  | emit b p ih =>
    simp only [Path.operand, Tm.bsubst_let₁, Tm.bsubst_op, Tm.bsubst_unit]
    exact congrArg (Tm.let₁ _) (ih _ _ _)
  | request req lf lt rf rt ilf ilt irf irt =>
    simp only [Path.operand, requestOperand, Bool.false_eq_true, ite_false,
      Tm.bsubst_case, Tm.bsubst_op, Tm.bsubst_unit, Tm.bsubst_bv, Tm.upSub_zero]
    rw [ilf, ilt, irf, irt]

private theorem const_case {m : Nat} {γ : BoundCtx Sorts m} {A : Sorts}
    {l r : Term (m + 1)} (b : Bool)
    (hl : HasType signature.Instr Γ₀ (γ.snoc U) l A) (hr : HasType signature.Instr Γ₀ (γ.snoc U) r A) :
    Equiv false Γ₀ γ (.case (bitOperand γ b).1 l r) ((if b then r else l).instantiate .unit) A := by
  cases b
  · exact (Equiv.caseBetaL .unit hl hr).trans (Equiv.letBeta .unit .unit hl)
  · exact (Equiv.caseBetaR .unit hl hr).trans (Equiv.letBeta .unit .unit hr)

private theorem select_case {k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m} {A : Sorts}
    {d : Term k} {l r : Term (k + 1)} {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ)
    (b : Bool) (hd : d.bsubst σ = (bitOperand γ b).1)
    (hl : HasType signature.Instr Γ₀ (β.snoc U) l A) (hr : HasType signature.Instr Γ₀ (β.snoc U) r A) :
    Equiv false Γ₀ γ ((Tm.case d l r).bsubst σ) ((if b then r else l).bsubst (Fin.cases .unit σ)) A := by
  rw [Tm.bsubst_case, hd]
  cases b
  · simpa only [Bool.false_eq_true, ite_false, instantiate_up] using
      const_case false (hl.bsubst (s.up U).typed) (hr.bsubst (s.up U).typed)
  · simpa only [ite_true, instantiate_up] using
      const_case true (hl.bsubst (s.up U).typed) (hr.bsubst (s.up U).typed)

private theorem matches_reply {k m n : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    {σ : Fin k → Term m} {slots : Retained β n} {env : Assignment n}
    (h : assignmentMatches γ slots σ env) (b : Bool) :
    assignmentMatches γ slots.bind (Fin.cases (bitOperand γ b).1 σ) (env.push b) :=
  Fin.cases rfl h

private theorem specialize_unit {k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ) :
    PureTypedSubst false Γ₀ (β.snoc U) γ (Fin.cases .unit σ) :=
  ⟨Fin.cases .unit s.typed, Fin.cases .unit s.pure⟩

private theorem specialize_bit {k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ) (b : Bool) :
    PureTypedSubst false Γ₀ (β.snoc Bit) γ (Fin.cases (bitOperand γ b).1 σ) :=
  ⟨Fin.cases (bitOperand γ b).2.toHasType s.typed, Fin.cases (bit_pure γ b) s.pure⟩

private theorem expr_specialize {n : Nat} (e : Expr n) {k m : Nat} {β : BoundCtx Sorts k}
    {γ : BoundCtx Sorts m} (slots : Retained β n) {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ)
    (env : Assignment n) (h : assignmentMatches γ slots σ env) :
    Equiv false Γ₀ γ ((e.operand slots).1.bsubst σ) (bitOperand γ (e.eval env)).1 Bit := by
  induction e generalizing k with
  | literal b =>
    rw [show ((Expr.literal b).operand slots).1 = (bitOperand β b).1 from rfl, literal_bsubst]
    exact .refl (bitOperand γ b).2.toHasType
  | read i =>
    change Equiv false Γ₀ γ (σ (slots i).1) (bitOperand γ (env i)).1 Bit
    rw [h i]
    exact .refl (bitOperand γ (env i)).2.toHasType
  | split l r ihl ihr =>
    let older : Retained (β.snoc U) _ := fun i => slots.weaken U i.succ
    have test := select_case (d := (slots.read 0).1) s (env 0) (h 0) (l.operand older).2.toHasType (r.operand older).2.toHasType
    have s' := specialize_unit s
    cases hb : env 0
    · simp only [hb, Bool.false_eq_true, ite_false] at test
      simp only [Expr.eval, hb, Bool.false_eq_true, ite_false]
      exact test.trans (ihl older s' env.tail (fun i => h i.succ))
    · simp only [hb, ite_true] at test
      simp only [Expr.eval, hb, ite_true]
      exact test.trans (ihr older s' env.tail (fun i => h i.succ))

private theorem canonical_arm {L : List Sorts} {m : Nat} (γ : BoundCtx Sorts m)
    (lo hi : Path L) (b : Bool) :
    Equiv false Γ₀ γ
      (Tm.instantiate
        (.case (.bv 0) (lo.operand ((γ.snoc Bit).snoc U)).1 (hi.operand ((γ.snoc Bit).snoc U)).1)
        (bitOperand γ b).1)
      ((if b then hi else lo).operand γ).1 (packedExitType L) := by
  unfold Tm.instantiate
  simp only [Tm.bsubst_case]
  rw [path_subst, path_subst]
  have reduce := const_case b (lo.operand (γ.snoc U)).2.toHasType (hi.operand (γ.snoc U)).2.toHasType
  cases b
  · simp only [Bool.false_eq_true, ite_false] at reduce ⊢
    rw [show (lo.operand (γ.snoc U)).1.instantiate .unit = (lo.operand γ).1 from path_subst lo _ _ _] at reduce
    exact reduce
  · simp only [ite_true] at reduce ⊢
    rw [show (hi.operand (γ.snoc U)).1.instantiate .unit = (hi.operand γ).1 from path_subst hi _ _ _] at reduce
    exact reduce

private theorem reply_arm {L : List Sorts} {k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    {a : Term (k + 1)} {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ)
    (ha : HasType signature.Instr Γ₀ (β.snoc Bit) a (packedExitType L)) (lo hi : Path L)
    (h₀ : Equiv false Γ₀ γ (a.bsubst (Fin.cases (bitOperand γ false).1 σ)) (lo.operand γ).1 (packedExitType L))
    (h₁ : Equiv false Γ₀ γ (a.bsubst (Fin.cases (bitOperand γ true).1 σ)) (hi.operand γ).1 (packedExitType L)) :
    Equiv false Γ₀ (γ.snoc Bit) (a.bsubst (Tm.upSub σ))
      (.case (.bv 0) (lo.operand ((γ.snoc Bit).snoc U)).1 (hi.operand ((γ.snoc Bit).snoc U)).1)
      (packedExitType L) := by
  let low := lo.operand ((γ.snoc Bit).snoc U)
  let high := hi.operand ((γ.snoc Bit).snoc U)
  apply bit_ext_proof (ha.bsubst (s.up Bit).typed) (.case .bv low.2.toHasType high.2.toHasType)
  · rw [instantiate_up]
    exact h₀.trans (canonical_arm γ lo hi false).symm
  · rw [instantiate_up]
    exact h₁.trans (canonical_arm γ lo hi true).symm

private theorem specialize_request {L : List Sorts} {k m n : Nat}
    {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m} (req : Bool) (l r : Normal L (n + 1))
    (slots : Retained β n) {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ)
    (env : Assignment n)
    (hl : ∀ b, Equiv false Γ₀ γ
      ((l.render.operand slots.bind).1.bsubst (Fin.cases (bitOperand γ b).1 σ))
      ((specialize l (env.push b)).operand γ).1 (packedExitType L))
    (hr : ∀ b, Equiv false Γ₀ γ
      ((r.render.operand slots.bind).1.bsubst (Fin.cases (bitOperand γ b).1 σ))
      ((specialize r (env.push b)).operand γ).1 (packedExitType L)) :
    Equiv false Γ₀ γ
      ((requestOperand req false (l.render.operand slots.bind) (r.render.operand slots.bind)).1.bsubst σ)
      ((Path.request req (specialize l (env.push false)) (specialize l (env.push true))
        (specialize r (env.push false)) (specialize r (env.push true))).operand γ).1 (packedExitType L) :=
  .case (.refl (.op .unit))
    (reply_arm s (l.render.operand slots.bind).2.toHasType _ _ (hl false) (hl true))
    (reply_arm s (r.render.operand slots.bind).2.toHasType _ _ (hr false) (hr true))

theorem specialize_normal_proof {L : List Sorts} {n : Nat} (p : Normal L n)
    {k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m} (slots : Retained β n)
    {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ)
    (env : Assignment n) (h : assignmentMatches γ slots σ env) :
    Equiv false Γ₀ γ ((p.render.operand slots).1.bsubst σ) ((specialize p env).operand γ).1 (packedExitType L) := by
  induction p generalizing k m with
  | ret pos table =>
    have run := expr_specialize (Expr.quote _ table) slots s env h
    rw [Expr.quote_eval] at run
    exact tag_subst_equiv L _ pos.typed _ _ σ run
  | emit b p ih =>
    have kept : assignmentMatches (γ.snoc U) (slots.weaken U) (Tm.upSub σ) env := fun i =>
      (congrArg Tm.lift (h i)).trans (literal_lift γ U (env i))
    exact .let₁ (.refl (.op .unit)) (ih (slots.weaken U) (s.up U) env kept)
  | request req l r ihl ihr =>
    exact specialize_request req l r slots s env
      (fun b => ihl slots.bind (specialize_bit s b) (env.push b) (matches_reply h b))
      (fun b => ihr slots.bind (specialize_bit s b) (env.push b) (matches_reply h b))
  | testRequest test low lf lr hf hr ilf ilr ihf ihr =>
    let kept := (slots.without test).weaken U
    let l := requestOperand low false (lf.render.operand kept.bind) (lr.render.operand kept.bind)
    let r := requestOperand (!low) false (hf.render.operand kept.bind) (hr.render.operand kept.bind)
    let rest := env.without test
    let s' := specialize_unit s
    have keptMatches : assignmentMatches γ kept (Fin.cases .unit σ) rest := fun i => h (test.succAbove i)
    have choose := select_case (d := (slots.read test).1) s (env test) (h test) l.2.toHasType r.2.toHasType
    cases hb : env test
    · simp only [hb, Bool.false_eq_true, ite_false] at choose
      have next := specialize_request low lf lr kept s' rest
        (fun b => ilf kept.bind (specialize_bit s' b) (rest.push b) (matches_reply keptMatches b))
        (fun b => ilr kept.bind (specialize_bit s' b) (rest.push b) (matches_reply keptMatches b))
      simp only [specialize, hb, Bool.false_eq_true, ite_false]
      exact choose.trans next
    · simp only [hb, ite_true] at choose
      have next := specialize_request (!low) hf hr kept s' rest
        (fun b => ihf kept.bind (specialize_bit s' b) (rest.push b) (matches_reply keptMatches b))
        (fun b => ihr kept.bind (specialize_bit s' b) (rest.push b) (matches_reply keptMatches b))
      simp only [specialize, hb, ite_true]
      exact choose.trans next

private theorem specialize_common {L : List Sorts} {n k m : Nat} {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m}
    (p : CommonRequest.Source L n) (slots : Retained β (n + 1)) (test : Fin (n + 1))
    {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ)
    (env : Assignment (n + 1)) (h : assignmentMatches γ slots σ env) :
    Equiv false Γ₀ γ ((p.operand slots test).1.bsubst σ)
      ((commonNormal p.normal test env).operand γ).1 (packedExitType L) := by
  refine ((p.replay slots test).bsubst s).trans ?_
  let q := p.normal
  let kept := (slots.without test).weaken U
  let l := requestOperand q.request false (q.arms.falseLeft.render.operand kept.bind)
    (q.arms.falseRight.render.operand kept.bind)
  let r := requestOperand q.request false (q.arms.trueLeft.render.operand kept.bind)
    (q.arms.trueRight.render.operand kept.bind)
  let rest := env.without test
  let s' := specialize_unit s
  have keptMatches : assignmentMatches γ kept (Fin.cases .unit σ) rest := fun i => h (test.succAbove i)
  have choose := select_case (d := (slots.read test).1) s (env test) (h test) l.2.toHasType r.2.toHasType
  have branch (left right : Normal L (n + 1)) :=
    specialize_request q.request left right kept s' rest
      (fun b => specialize_normal_proof left kept.bind (specialize_bit s' b) (rest.push b) (matches_reply keptMatches b))
      (fun b => specialize_normal_proof right kept.bind (specialize_bit s' b) (rest.push b) (matches_reply keptMatches b))
  cases hb : env test
  · simp only [hb, Bool.false_eq_true, ite_false] at choose
    simp only [commonNormal, hb, Bool.false_eq_true, ite_false]
    exact choose.trans (branch q.arms.falseLeft q.arms.falseRight)
  · simp only [hb, ite_true] at choose
    simp only [commonNormal, hb, ite_true]
    exact choose.trans (branch q.arms.trueLeft q.arms.trueRight)

theorem specialize_source_proof {L : List Sorts} {n k m : Nat}
    {β : BoundCtx Sorts k} {γ : BoundCtx Sorts m} (p : Source L n) (slots : Retained β n)
    {σ : Fin k → Term m} (s : PureTypedSubst false Γ₀ β γ σ)
    (env : Assignment n) (h : assignmentMatches γ slots σ env) :
    Equiv false Γ₀ γ ((p.operand slots).1.bsubst σ) ((p.normal env).operand γ).1 (packedExitType L) := by
  cases p with
  | tree t => exact ((t.replay slots).bsubst s).trans (specialize_normal_proof t.normal slots s env h)
  | common test t => exact specialize_common t slots test s env h

private theorem bitSlots_index (n : Nat) (i : Fin n) : (CommonRequest.bitSlots n i).1 = i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih => exact Fin.cases rfl (fun j => congrArg Fin.succ (ih j)) i

private theorem literal_typed {n : Nat} (env : Assignment n) :
    PureTypedSubst false Γ₀ (CommonRequest.bitCtx n) .nil (literalSubst .nil env) where
  typed i := by
    have slot := (CommonRequest.bitSlots n i).2
    rw [bitSlots_index] at slot
    rw [slot]
    exact (bitOperand .nil (env i)).2.toHasType
  pure i := bit_pure .nil (env i)

theorem derive_normal_proof (H : Sorts) (L : List Sorts) {n : Nat} (p q : Source (H :: L) n)
    (h : ∀ env, p.normal env = q.normal env) : Derivable false (equation H L p q) := by
  let slots := CommonRequest.bitSlots n
  have matched (env : Assignment n) : assignmentMatches .nil slots (literalSubst .nil env) env :=
    fun a => congrArg (literalSubst .nil env) (bitSlots_index _ a)
  have entries := assignments_ext_proof (p.operand slots).2.toHasType (q.operand slots).2.toHasType
    (fun env => by
      have left := specialize_source_proof p slots (literal_typed env) env (matched env)
      have right := specialize_source_proof q slots (literal_typed env) env (matched env)
      rw [h env] at left
      exact left.trans right.symm)
  exact .let₁ entries (.refl ((program H L p).body.render .base).encode.toLetCase.2.toHasType)

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.Extensional
