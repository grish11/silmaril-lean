module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Defs
public import Silmaril.SSA.Isotope.LetCase.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Recursive.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.SumBind.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.ProductBind.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.ConstructorJoin.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.OrderedPairs.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Region (HasType ValueBranches)
open Region.Paper
open Silmaril.DeBruijn (lift)
open Region.Paper.RetainedLet (returnOnce)
open Region.Paper.RetainedCase (boundCase)
open Region.Paper.WithComputedCallReturns
open Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding (mapSeed)
open Region.Paper.UnaryReturn.Beta.Constructors (pairSequence)
open Native Native.SumBind
open Morphism.CaseSSA (erase erase_hasType)
open LetCase.LocallyNameless (CoreAxiom Derivation Equiv)
local notation "CaseTm" => LetCase.LocallyNameless.Tm Empty
local notation "CaseType" => LetCase.LocallyNameless.HasType

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}
  {Γ : VCtx (Ty α)} {A B D : Ty α} {a a' b b' : Tm Φ}

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty α))
local notation "Typed" => Tm.HasType
local notation "ReturnEq" => fun (Γ : VCtx (Ty α)) (a b : Tm Φ) (A : Ty α) =>
  ReplayEqv pe Γ (returnOnce a) (returnOnce b) [A]

private theorem operand {L : LCtx (Ty α)} {r s : Region Φ}
    (h : Continuation.Eqv pe Γ r s L) : ReplayEqv pe Γ r s L := mapSeed Or.inr h

private theorem ordered {L : LCtx (Ty α)} {r s : Region Φ}
    (h : OrderedPairs.Eqv pe Γ r s L) : ReplayEqv pe Γ r s L :=
  operand (Continuation.ofSums (SumBind.ofProducts (ProductBind.ofPairs h)))

private theorem unary_seed {L : LCtx (Ty α)} {r s : Region Φ}
    (h : UnaryReturn.Step Γ r s L) : ReplaySeed pe Γ r s L :=
  .inr (.inl (.inl (.inl (.inl (.inl (.inl (.inr (.inl h))))))))

private theorem split_let (ha : Typed Γ a A) (hb : Typed (A :: Γ) b B) :
    ReplayEqv pe Γ (returnOnce (.let₁ a b)) (.let₁ a (returnOnce b)) [B] :=
  let step := UnaryReturn.Step.fuse ha hb
  (Extension.Eqv.extra step.typed.1 step.typed.2 (unary_seed step)).symm

theorem return_refl (ha : Typed Γ a A) : ReturnEq Γ a a A :=
  .refl (UnaryReturn.returnOnce_valueBranches ha).hasType

private theorem post_return {L : LCtx (Ty α)} {r k : Region Φ}
    (ha : Typed Γ a A) (hr : ValueBranches Γ r [A])
    (e : ReplayEqv pe Γ (returnOnce a) r [A]) (hk : HasType (A :: Γ) k L) :
    ReplayEqv pe Γ (.let₁ a k) (r.lsubst (fun _ => k)) L := by
  have typed (i : Nat) (T : Ty α) (hit : At [A] i T) : HasType (T :: Γ) k L :=
    (List.mem_singleton.mp (List.mem_of_getElem? hit)).symm ▸ hk
  have out := Extension.Eqv.lsubstPost e (UnaryReturn.returnOnce_valueBranches ha) hr typed
  change ReplayEqv pe Γ ((Region.br 0 a).bindBranchArguments.lsubst (fun _ => k)) _ L at out
  rw [Region.lsubst_bindBranchArguments_br] at out
  exact out

/-- Continuation substitution gives congruence for the producer of a binder. -/
private theorem bind_congr {L : LCtx (Ty α)} {r s : Region Φ}
    (ha : Typed Γ a A) (ha' : Typed Γ a' A) (e : ReturnEq Γ a a' A)
    (k : ReplayEqv pe (A :: Γ) r s L) :
    ReplayEqv pe Γ (.let₁ a r) (.let₁ a' s) L := by
  have out := post_return ha (UnaryReturn.returnOnce_valueBranches ha') e k.typed.2
  change ReplayEqv pe Γ (.let₁ a s) ((Region.br 0 a').bindBranchArguments.lsubst (fun _ => s)) L at out
  rw [Region.lsubst_bindBranchArguments_br] at out
  exact (Extension.Eqv.let₁ ha k).trans out

/-- Splicing below a binder weakens the captures but leaves the result slot at zero. -/
private theorem post_let {k : Region Φ} :
    (Region.let₁ a (returnOnce b)).lsubst (fun _ => k) =
      .let₁ a (.let₁ b (k.renameVars (lift Nat.succ))) := by
  change Region.let₁ a ((Region.br 0 b).bindBranchArguments.lsubst
    (Region.liftLSubstVars (fun _ => k))) = _
  rw [Region.lsubst_bindBranchArguments_br]
  rfl

private theorem post_let₂ {k : Region Φ} :
    (Region.let₂ a (returnOnce b)).lsubst (fun _ => k) =
      .let₂ a (.let₁ b ((k.renameVars (lift Nat.succ)).renameVars (lift Nat.succ))) := by
  change Region.let₂ a ((Region.br 0 b).bindBranchArguments.lsubst
    (Region.liftLSubstVars (Region.liftLSubstVars (fun _ => k)))) = _
  rw [Region.lsubst_bindBranchArguments_br]
  rfl

private theorem post_case {l r : Tm Φ} {k : Region Φ} :
    (Region.case a (returnOnce l) (returnOnce r)).lsubst (fun _ => k) =
      .case a (.let₁ l (k.renameVars (lift Nat.succ))) (.let₁ r (k.renameVars (lift Nat.succ))) := by
  change Region.case a ((Region.br 0 l).bindBranchArguments.lsubst (Region.liftLSubstVars (fun _ => k)))
    ((Region.br 0 r).bindBranchArguments.lsubst (Region.liftLSubstVars (fun _ => k))) = _
  rw [Region.lsubst_bindBranchArguments_br, Region.lsubst_bindBranchArguments_br]
  rfl

private theorem erase_under {n : Nat} (t : CaseTm Φ (n + 1)) :
    erase t.underBinder = (erase t).rename (lift Nat.succ) :=
  Morphism.CaseSSA.erase_rename _ _ (Fin.cases rfl (fun _ => rfl)) t

private theorem erase_under₂ {n : Nat} (t : CaseTm Φ (n + 2)) :
    erase t.underTwoBinders = (erase t).rename (lift (lift Nat.succ)) :=
  Morphism.CaseSSA.erase_rename _ _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) t

theorem let_congr (ha : Typed Γ a A) (ha' : Typed Γ a' A)
    (hb : Typed (A :: Γ) b B) (hb' : Typed (A :: Γ) b' B)
    (e : ReturnEq Γ a a' A) (k : ReturnEq (A :: Γ) b b' B) :
    ReturnEq Γ (.let₁ a b) (.let₁ a' b') B :=
  (split_let ha hb).trans ((bind_congr ha ha' e k).trans (split_let ha' hb').symm)

private theorem split_op (f : Φ) (ha : Typed Γ a (instrSrc f)) :
    ReplayEqv pe Γ (returnOnce (.op f a)) (.let₁ a (returnOnce (.op f (.var 0)))) [instrTrg f] := by
  have newest : Typed (instrSrc f :: Γ) (.op f (.var 0)) (instrTrg f) := .op (.var (i := 0) rfl)
  exact (ordered (OrderedPairs.ofCalls (ConstructorJoin.ofCall (Step.seq f ha)))).trans
    ((UnaryReturn.returnRegion_eq_returnOnce unary_seed (.let₁ ha newest)).trans (split_let ha newest))

private theorem op_congr (f : Φ) (ha : Typed Γ a (instrSrc f)) (ha' : Typed Γ a' (instrSrc f))
    (e : ReturnEq Γ a a' (instrSrc f)) : ReturnEq Γ (.op f a) (.op f a') (instrTrg f) :=
  (split_op f ha).trans ((bind_congr ha ha' e (return_refl
    (.op (f := f) (.var (i := 0) rfl)))).trans (split_op f ha').symm)

private theorem pair_split (ha : Typed Γ a A) (hb : Typed Γ b B) :
    ReplayEqv pe Γ (returnOnce (.pair a b)) (pairSequence a b) [Ty.product A B] :=
  ordered (.extra (UnaryReturn.returnOnce_valueBranches (.pair ha hb)).hasType
    (WithPairReturns.pairSequence_typed ha hb).hasType (.inr (.seq ha hb)))

theorem pair_congr (ha : Typed Γ a A) (ha' : Typed Γ a' A)
    (hb : Typed Γ b B) (hb' : Typed Γ b' B)
    (e : ReturnEq Γ a a' A) (k : ReturnEq Γ b b' B) :
    ReturnEq Γ (.pair a b) (.pair a' b') (Ty.product A B) := by
  have moved : ReturnEq (A :: Γ) (b.rename Nat.succ) (b'.rename Nat.succ) B :=
    k.renameVars (Ren.wk Γ A)
  have tail : HasType (B :: A :: Γ) (.br 0 (.pair (.var 1) (.var 0)) : Region Φ) [Ty.product A B] :=
    .br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))
  have both := bind_congr ha ha' e (bind_congr (hb.rename (Ren.wk Γ A)) (hb'.rename (Ren.wk Γ A))
    moved (.refl tail))
  exact (pair_split ha hb).trans (both.trans (pair_split ha' hb').symm)

theorem let₂_congr (ha : Typed Γ a (Ty.product A B)) (ha' : Typed Γ a' (Ty.product A B))
    (hb : Typed (B :: A :: Γ) b D) (hb' : Typed (B :: A :: Γ) b' D)
    (e : ReturnEq Γ a a' (Ty.product A B)) (k : ReturnEq (B :: A :: Γ) b b' D) :
    ReturnEq Γ (.let₂ a b) (.let₂ a' b') D := by
  have move := ProductBind.bind_replay_with (seed := ReplaySeed pe)
    (fun h => .inr (.inl (.inl (.inr h)))) ha (UnaryReturn.returnOnce_valueBranches ha') e k
  have right := ProductBind.bind_replay_with (seed := ReplaySeed pe)
    (fun h => .inr (.inl (.inl (.inr h)))) ha' (UnaryReturn.returnOnce_valueBranches ha') (return_refl ha')
    (return_refl hb')
  exact (operand (Continuation.split_let₂ ha hb)).trans
    (move.trans (right.symm.trans (operand (Continuation.split_let₂ ha' hb')).symm))

theorem inl_congr (ha : Typed Γ a A) (ha' : Typed Γ a' A) (e : ReturnEq Γ a a' A) :
    ReturnEq Γ (.inl a) (.inl a') (Ty.coprod A B) := by
  have tail : HasType (A :: Γ) (.br 0 (.inl (.var 0)) : Region Φ) [Ty.coprod A B] :=
    .br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))
  exact (operand (Continuation.split_inl ha)).trans
    ((bind_congr ha ha' e (.refl tail)).trans (operand (Continuation.split_inl ha')).symm)

theorem inr_congr (ha : Typed Γ a B) (ha' : Typed Γ a' B) (e : ReturnEq Γ a a' B) :
    ReturnEq Γ (.inr a) (.inr a') (Ty.coprod A B) := by
  have tail : HasType (B :: Γ) (.br 0 (.inr (.var 0)) : Region Φ) [Ty.coprod A B] :=
    .br (ℓ := 0) rfl (.inr (.var (i := 0) rfl))
  exact (operand (Continuation.split_inr ha)).trans
    ((bind_congr ha ha' e (.refl tail)).trans (operand (Continuation.split_inr ha')).symm)

theorem case_congr {e e' l l' r r' : Tm Φ}
    (he : Typed Γ e (Ty.coprod A B)) (he' : Typed Γ e' (Ty.coprod A B))
    (hl : Typed (A :: Γ) l D) (hl' : Typed (A :: Γ) l' D)
    (hr : Typed (B :: Γ) r D) (hr' : Typed (B :: Γ) r' D)
    (scr : ReturnEq Γ e e' (Ty.coprod A B)) (left : ReturnEq (A :: Γ) l l' D) (right : ReturnEq (B :: Γ) r r' D) :
    ReturnEq Γ (.case e l r) (.case e' l' r') D := by
  have leftValue := UnaryReturn.returnOnce_valueBranches hl'
  have rightValue := UnaryReturn.returnOnce_valueBranches hr'
  have bind (a : Tm Φ) (ha : Typed Γ a (Ty.coprod A B)) :=
    WithCaseBind.case_eq_let (Seed := ReplaySeed pe) (fun h => .inr (.inl (.inr h))) ha leftValue rightValue
  have lsplit := operand (pe := pe) (Continuation.split_return he hl hr)
  have rsplit := operand (pe := pe) (Continuation.split_return he' hl' hr')
  have forward := (lsplit.trans (.case he left right)).trans (bind e he)
  have body : HasType (Ty.coprod A B :: Γ) (boundCase (returnOnce l') (returnOnce r')) [D] :=
    .case (.var (i := 0) rfl) (leftValue.hasType.renameVars ((Ren.wk Γ (Ty.coprod A B)).lift A))
      (rightValue.hasType.renameVars ((Ren.wk Γ (Ty.coprod A B)).lift B))
  exact forward.trans ((bind_congr he he' scr (.refl body)).trans ((bind e' he').symm.trans rsplit.symm))

private theorem abort_congr (ha : Typed Γ a Ty.empty) (ha' : Typed Γ a' Ty.empty)
    (e : ReturnEq Γ a a' Ty.empty) : ReturnEq Γ (.abort a) (.abort a') D := by
  have tail : Typed (Ty.empty :: Γ) (.abort (.var 0) : Tm Φ) D := .abort (.var (i := 0) rfl)
  exact (operand (Continuation.split_abort ha)).trans
    ((bind_congr ha ha' e (return_refl tail)).trans (operand (Continuation.split_abort ha')).symm)

private theorem let_eta (ha : Typed Γ a A) : ReturnEq Γ (.let₁ a (.var 0)) a A :=
  (split_let ha (.var (i := 0) rfl)).trans
    (.let₁ ha (.paper (.cfgEta (.native (.letValue (.var (i := 0) rfl)
      (.br (ℓ := 0) rfl (.var (i := 0) rfl)))))))

theorem case_beta_left {l r : Tm Φ} (ha : Typed Γ a A) (hl : Typed (A :: Γ) l D)
    (hr : Typed (B :: Γ) r D) : ReturnEq Γ (.case (.inl a) l r) (.let₁ a l) D :=
  (operand (Continuation.split_return (.inl ha) hl hr)).trans
    ((Extension.Eqv.paper (.cfgEta (.native (.base (.caseInl ha (UnaryReturn.returnOnce_valueBranches hl).hasType
      (UnaryReturn.returnOnce_valueBranches hr).hasType))))).trans (split_let ha hl).symm)

theorem case_beta_right {l r : Tm Φ} (ha : Typed Γ a B) (hl : Typed (A :: Γ) l D)
    (hr : Typed (B :: Γ) r D) : ReturnEq Γ (.case (.inr a) l r) (.let₁ a r) D :=
  (operand (Continuation.split_return (.inr ha) hl hr)).trans
    ((Extension.Eqv.paper (.cfgEta (.native (.base (.caseInr ha (UnaryReturn.returnOnce_valueBranches hl).hasType
      (UnaryReturn.returnOnce_valueBranches hr).hasType))))).trans (split_let ha hr).symm)

private theorem return_value (ha : Tm.BranchValue Γ a A) :
    ReplayEqv pe Γ (returnOnce a) (.br 0 a) [A] :=
  .paper (.cfgEta (.native (.letValue ha (.br (ℓ := 0) rfl (.var (i := 0) rfl)))))

theorem unit_branch (h : Tm.BranchValue Γ a Ty.unit) :
    ReplayEqv pe Γ (.br 0 .unit) (.br 0 a) [Ty.unit] := by
  have η := WithUnitEta.branch_unit_eta h (rfl : At [Ty.unit] 0 (Ty.unit : Ty α))
  have includeUnit {Δ : VCtx (Ty α)} {K : LCtx (Ty α)} {r s : Region Φ} :
      WithUnitEta.Step Δ r s K → ReplaySeed pe Δ r s K :=
    fun e => .inr (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr e))))))))
  exact WithProjectionReturnsAndUnitEta.WithBranchBinding.mapSeed includeUnit η

theorem unit_eta (ha : Typed Γ a Ty.unit) : ReturnEq Γ (.let₁ a .unit) a Ty.unit :=
  (split_let ha .unit).trans (.let₁ ha ((return_value .unit).trans (unit_branch (.var (i := 0) rfl))))

private theorem bind_let {c : Tm Φ} (ha : Typed Γ a A) (hb : Typed (A :: Γ) b B)
    (hc : Typed (B :: Γ) c D) :
    ReturnEq Γ (.let₁ (.let₁ a b) c) (.let₁ a (.let₁ b (c.rename (lift Nat.succ)))) D := by
  have fresh := hc.rename ((Ren.wk Γ A).lift B)
  have move := post_return (pe := pe) (.let₁ ha hb) (.let₁ ha (UnaryReturn.returnOnce_valueBranches hb))
    (split_let ha hb) (UnaryReturn.returnOnce_valueBranches hc).hasType
  rw [post_let] at move
  exact (split_let (.let₁ ha hb) hc).trans (move.trans
    ((Extension.Eqv.let₁ ha (split_let hb fresh).symm).trans (split_let ha (.let₁ hb fresh)).symm))

private theorem bind_op (f : Φ) {c : Tm Φ} (ha : Typed Γ a (instrSrc f)) (hc : Typed (instrTrg f :: Γ) c D) :
    ReturnEq Γ (.let₁ (.op f a) c)
      (.let₁ a (.let₁ (.op f (.var 0)) (c.rename (lift Nat.succ)))) D := by
  have call : Typed (instrSrc f :: Γ) (.op f (.var 0)) (instrTrg f) := .op (.var (i := 0) rfl)
  have fresh := hc.rename ((Ren.wk Γ (instrSrc f)).lift (instrTrg f))
  have move := post_return (pe := pe) (.op ha) (.let₁ ha (UnaryReturn.returnOnce_valueBranches call))
    (split_op f ha) (UnaryReturn.returnOnce_valueBranches hc).hasType
  rw [post_let] at move
  exact (split_let (.op ha) hc).trans (move.trans
    ((Extension.Eqv.let₁ ha (split_let call fresh).symm).trans (split_let ha (.let₁ call fresh)).symm))

private theorem bind_let_pair {c : Tm Φ} (ha : Typed Γ a (Ty.product A B)) (hb : Typed (B :: A :: Γ) b D)
    {E : Ty α} (hc : Typed (D :: Γ) c E) :
    ReturnEq Γ (.let₁ (.let₂ a b) c)
      (.let₂ a (.let₁ b ((c.rename (lift Nat.succ)).rename (lift Nat.succ)))) E := by
  have fresh := (hc.rename ((Ren.wk Γ A).lift D)).rename ((Ren.wk (A :: Γ) B).lift D)
  have move := post_return (pe := pe) (.let₂ ha hb) (.let₂ ha (UnaryReturn.returnOnce_valueBranches hb))
    (operand (Continuation.split_let₂ ha hb)) (UnaryReturn.returnOnce_valueBranches hc).hasType
  rw [post_let₂] at move
  exact (split_let (.let₂ ha hb) hc).trans (move.trans
    ((Extension.Eqv.let₂ ha (split_let hb fresh).symm).trans (operand (Continuation.split_let₂ ha (.let₁ hb fresh))).symm))

private theorem bind_let_case {e l r k : Tm Φ} (he : Typed Γ e (Ty.coprod A B))
    (hl : Typed (A :: Γ) l D) (hr : Typed (B :: Γ) r D) {E : Ty α} (hk : Typed (D :: Γ) k E) :
    ReturnEq Γ (.let₁ (.case e l r) k)
      (.case e (.let₁ l (k.rename (lift Nat.succ))) (.let₁ r (k.rename (lift Nat.succ)))) E := by
  have lk := hk.rename ((Ren.wk Γ A).lift D)
  have rk := hk.rename ((Ren.wk Γ B).lift D)
  have move := post_return (pe := pe) (.case he hl hr)
    (.case he (UnaryReturn.returnOnce_valueBranches hl) (UnaryReturn.returnOnce_valueBranches hr))
    (operand (Continuation.split_return he hl hr)) (UnaryReturn.returnOnce_valueBranches hk).hasType
  rw [post_case] at move
  exact (split_let (.case he hl hr) hk).trans (move.trans
    ((Extension.Eqv.case he (split_let hl lk).symm (split_let hr rk).symm).trans
      (operand (Continuation.split_return he (.let₁ hl lk) (.let₁ hr rk))).symm))

private theorem bind_pair (ha : Typed Γ a (Ty.product A B)) (hb : Typed (B :: A :: Γ) b D) :
    ReturnEq Γ (.let₂ a b) (.let₁ a (.let₂ (.var 0) (b.rename (lift (lift Nat.succ))))) D := by
  let value := UnaryReturn.returnOnce_valueBranches hb
  let step := Region.BinaryLetBind.Step.bind ha value.hasType
  have moved := hb.rename (((Ren.wk Γ (Ty.product A B)).lift A).lift B)
  have exposed : Typed (Ty.product A B :: Γ) (.let₂ (.var 0) (b.rename (lift (lift Nat.succ)))) D :=
    .let₂ (.var (i := 0) rfl) moved
  have law : ReplayEqv pe Γ (.let₂ a (returnOnce b))
      (.let₁ a (.let₂ (.var 0) (returnOnce (b.rename (lift (lift Nat.succ)))))) [D] :=
    .extra step.typed.1 step.typed.2 (.inr (.inl (.inl (.inr step))))
  exact (operand (Continuation.split_let₂ ha hb)).trans (law.trans
    ((Extension.Eqv.let₁ ha (operand (Continuation.split_let₂ (.var (i := 0) rfl) moved)).symm).trans
      (split_let ha exposed).symm))

private theorem bind_case (he : Typed Γ a (Ty.coprod A B)) (hl : Typed (A :: Γ) b D)
    {c : Tm Φ} (hr : Typed (B :: Γ) c D) :
    ReturnEq Γ (.case a b c)
      (.let₁ a (.case (.var 0) (b.rename (lift Nat.succ)) (c.rename (lift Nat.succ)))) D := by
  have lv := hl.rename ((Ren.wk Γ (Ty.coprod A B)).lift A)
  have rv := hr.rename ((Ren.wk Γ (Ty.coprod A B)).lift B)
  have scr : Typed (Ty.coprod A B :: Γ) (.var 0 : Tm Φ) (Ty.coprod A B) := .var (i := 0) rfl
  have step := WithCaseBind.case_eq_let (Seed := ReplaySeed pe) (fun h => .inr (.inl (.inr h)))
    he (UnaryReturn.returnOnce_valueBranches hl) (UnaryReturn.returnOnce_valueBranches hr)
  exact (operand (Continuation.split_return he hl hr)).trans (step.trans
    ((Extension.Eqv.let₁ he (operand (Continuation.split_return scr lv rv)).symm).trans
      (split_let he (.case scr lv rv)).symm))

private theorem pair_eta (ha : Typed Γ a (Ty.product A B)) :
    ReturnEq Γ (.let₂ a (.pair (.var 1) (.var 0))) a (Ty.product A B) := by
  let P := Ty.product A B
  have fields : Tm.BranchValue (B :: A :: P :: Γ) (.pair (.var 1) (.var 0) : Tm Φ) P :=
    .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  have rebuild : Typed (P :: Γ) (.let₂ (.var 0) (.pair (.var 1) (.var 0)) : Tm Φ) P :=
    .let₂ (.var (i := 0) rfl) fields.hasType
  have eta : ReplayEqv pe (P :: Γ) (.let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))))
      (.br 0 (.var 0)) [P] := .paper (.productEta (Region.ProductEta.Step.let₂Eta (Φ := Φ) (i := 0) (ℓ := 0) (A := A) (B := B) rfl rfl))
  exact (bind_pair ha (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))).trans
    ((split_let ha rebuild).trans (.let₁ ha ((operand (Continuation.split_let₂ (.var (i := 0) rfl) fields.hasType)).trans
      ((Extension.Eqv.let₂ (.var (i := 0) rfl) (return_value fields)).trans eta))))

theorem case_eta (ha : Typed Γ a (Ty.coprod A B)) :
    ReturnEq Γ (.case a (.inl (.var 0)) (.inr (.var 0))) a (Ty.coprod A B) := by
  let S := Ty.coprod A B
  have scr : Tm.BranchValue (S :: Γ) (.var 0 : Tm Φ) S := .var (i := 0) rfl
  have lv : Tm.BranchValue (A :: S :: Γ) (.inl (.var 0) : Tm Φ) S := .inl (.var (i := 0) rfl)
  have rv : Tm.BranchValue (B :: S :: Γ) (.inr (.var 0) : Tm Φ) S := .inr (.var (i := 0) rfl)
  have eta : ReplayEqv pe (S :: Γ) (.case (.var 0) (.br 0 (.inl (.var 0))) (.br 0 (.inr (.var 0))))
      (.br 0 (.var 0)) [S] := .paper (.cfgEta (.native (.caseValue scr (.br (ℓ := 0) rfl (.var (i := 0) rfl)))))
  exact (bind_case ha (.inl (.var (i := 0) rfl)) (.inr (.var (i := 0) rfl))).trans
    ((split_let ha (.case scr.hasType lv.hasType rv.hasType)).trans
      (.let₁ ha ((operand (Continuation.split_return scr.hasType lv.hasType rv.hasType)).trans
        ((Extension.Eqv.case scr.hasType (return_value lv) (return_value rv)).trans eta))))

private theorem empty_initial (ha : Typed Γ a Ty.empty)
    (hb : Typed (A :: Γ) b D) {c : Tm Φ} (hc : Typed (B :: Γ) c D) :
    ReturnEq Γ (.let₁ (.abort a) b) (.let₁ (.abort a) c) D := by
  have stop (X : Ty α) : Typed (Ty.empty :: Γ) (.abort (.var 0) : Tm Φ) X := .abort (.var (i := 0) rfl)
  have toEmpty {t : Tm Φ} {X : Ty α} (ht : Typed (X :: Γ) t D) :
      ReplayEqv pe Γ (returnOnce (.let₁ (.abort a) t))
        (.let₁ a (.let₁ (.abort (.var 0)) ((returnOnce t).renameVars (lift Nat.succ)))) [D] := by
    have e := post_return (pe := pe) (.abort ha) (.let₁ ha (UnaryReturn.returnOnce_valueBranches (stop X)))
      (operand (Continuation.split_abort ha)) (UnaryReturn.returnOnce_valueBranches ht).hasType
    rw [post_let] at e
    exact (split_let (.abort ha) ht).trans e
  have unreachable (t : Tm Φ) {X : Ty α} (ht : Typed (X :: Γ) t D) :
      HasType (Ty.empty :: Γ)
        (.let₁ (.abort (.var 0)) ((returnOnce t).renameVars (lift Nat.succ))) [D] :=
    .let₁ (stop X) ((UnaryReturn.returnOnce_valueBranches ht).hasType.renameVars ((Ren.wk Γ Ty.empty).lift X))
  have same : ReplayEqv pe (Ty.empty :: Γ) _ _ [D] :=
    .paper (.cfgEta (.native (.initial (.var (i := 0) rfl) (unreachable b hb) (unreachable c hc))))
  exact (toEmpty hb).trans ((Extension.Eqv.let₁ ha same).trans (toEmpty hc).symm)

/-- The freshly evaluated pair fields substitute into the rebound continuation in right-left slot order. -/
private theorem splice_pair_beta {c : Tm Φ} :
    (pairSequence a b).lsubst (fun _ => ProductBind.unpack (returnOnce c)) =
      .let₁ a (.let₁ (b.rename Nat.succ)
        (.let₂ (.pair (.var 1) (.var 0))
          ((returnOnce c).renameVars (lift (lift (Nat.succ ∘ Nat.succ)))))) := by
  change Region.let₁ a (.let₁ (b.rename Nat.succ)
    (Region.let₂ (.var 0) (((returnOnce c).renameVars (lift (lift Nat.succ))).renameVars
      (lift (lift (lift Nat.succ))) |>.renameVars (lift (lift (lift Nat.succ)))) |>.substVars
        (Tm.singleSubst (.pair (.var 1) (.var 0))))) = _
  simp only [Region.substVars]
  rw [Region.renameVars_comp, Region.renameVars_comp, Region.substVars_renameVars]
  rw [Region.renameVars_eq_substVars]
  have indices : Tm.liftSubstN 2 (Tm.singleSubst (.pair (.var 1) (.var 0) : Tm Φ)) ∘
      ((lift (lift (lift Nat.succ)) ∘ lift (lift (lift Nat.succ))) ∘ lift (lift Nat.succ)) =
      Tm.var ∘ lift (lift (Nat.succ ∘ Nat.succ)) := by
    funext i
    match i with
    | 0 | 1 | _ + 2 => rfl
  rw [indices]
  rfl

private theorem pair_beta {c : Tm Φ} (ha : Typed Γ a A) (hb : Typed Γ b B)
    (hc : Typed (B :: A :: Γ) c D) :
    ReturnEq Γ (.let₂ (.pair a b) c) (.let₁ a (.let₁ (b.rename Nat.succ) c)) D := by
  have body := UnaryReturn.returnOnce_valueBranches hc
  have moved := ProductBind.bind_replay_with (seed := ReplaySeed pe)
    (fun h => .inr (.inl (.inl (.inr h)))) (.pair ha hb)
    (WithPairReturns.pairSequence_typed ha hb) (pair_split ha hb) (return_refl hc)
  rw [splice_pair_beta] at moved
  let Δ := B :: A :: Γ
  have l : Tm.BranchValue Δ (.var 1 : Tm Φ) A := .var (i := 1) rfl
  have r : Tm.BranchValue Δ (.var 0 : Tm Φ) B := .var (i := 0) rfl
  have rename := Ren.wk Γ A |>.comp (Ren.wk (A :: Γ) B)
  have β := Extension.Eqv.paper (Seed := ReplaySeed pe)
    (.productBeta (.let₂Beta l r (body.hasType.renameVars ((rename.lift A).lift B))))
  change ReplayEqv pe Δ
    (.let₂ (.pair (.var 1) (.var 0)) ((returnOnce c).renameVars (lift (lift (Nat.succ ∘ Nat.succ))))) _ [D] at β
  rw [Region.substVars_renameVars] at β
  have drop : Tm.consSubst (.var 0 : Tm Φ) (Tm.singleSubst (.var 1)) ∘
      lift (lift (Nat.succ ∘ Nat.succ)) = Tm.var := by
    funext i
    match i with
    | 0 | 1 | _ + 2 => rfl
  rw [drop, Region.substVars_var] at β
  have next := hb.rename (Ren.wk Γ A)
  exact (operand (Continuation.split_let₂ (.pair ha hb) hc)).trans (moved.trans
    ((Extension.Eqv.let₁ ha (.let₁ next β)).trans
      ((Extension.Eqv.let₁ ha (split_let next hc).symm).trans (split_let ha (.let₁ next hc)).symm)))

/-- Substitute term comparisons through all exact constructors. Renaming under
each binder preserves its newest slot and weakens both compared images. -/
private theorem subst_return {Δ : VCtx (Ty α)} {σ υ : Nat → Tm Φ} (h : Typed Γ a A)
    (hσ : Tm.Subst.HasType Γ Δ σ) (hυ : Tm.Subst.HasType Γ Δ υ)
    (e : ∀ ⦃i T⦄, At Γ i T → ReturnEq Δ (σ i) (υ i) T) :
    ReturnEq Δ (a.subst σ) (a.subst υ) A := by
  have liftEq {Ξ Ξ' : VCtx (Ty α)} {θ η : Nat → Tm Φ} (T : Ty α)
      (he : ∀ ⦃i A⦄, At Ξ i A → ReturnEq Ξ' (θ i) (η i) A) :
      ∀ ⦃i A⦄, At (T :: Ξ) i A → ReturnEq (T :: Ξ') (Tm.liftSubst θ i) (Tm.liftSubst η i) A := by
    intro i X hi
    cases i with
    | zero => exact return_refl (.var hi)
    | succ i => exact (he hi).renameVars (Ren.wk Ξ' T)
  induction h generalizing Δ σ υ with
  | var hi => exact e hi
  | unit => exact return_refl .unit
  | op ht ih => exact op_congr _ (ht.subst hσ) (ht.subst hυ) (ih hσ hυ e)
  | let₁ ha hb ia ib =>
    exact let_congr (ha.subst hσ) (ha.subst hυ) (hb.subst (hσ.lift _)) (hb.subst (hυ.lift _))
      (ia hσ hυ e) (ib (hσ.lift _) (hυ.lift _) (liftEq _ e))
  | let₂ ha hb ia ib =>
    exact let₂_congr (ha.subst hσ) (ha.subst hυ) (hb.subst ((hσ.lift _).lift _)) (hb.subst ((hυ.lift _).lift _))
      (ia hσ hυ e) (ib ((hσ.lift _).lift _) ((hυ.lift _).lift _) (liftEq _ (liftEq _ e)))
  | pair ha hb ia ib =>
    exact pair_congr (ha.subst hσ) (ha.subst hυ) (hb.subst hσ) (hb.subst hυ) (ia hσ hυ e) (ib hσ hυ e)
  | inl ha ih => exact inl_congr (ha.subst hσ) (ha.subst hυ) (ih hσ hυ e)
  | inr ha ih => exact inr_congr (ha.subst hσ) (ha.subst hυ) (ih hσ hυ e)
  | case he hl hr ie il ir =>
    exact case_congr (he.subst hσ) (he.subst hυ)
      (hl.subst (hσ.lift _)) (hl.subst (hυ.lift _)) (hr.subst (hσ.lift _)) (hr.subst (hυ.lift _))
      (ie hσ hυ e) (il (hσ.lift _) (hυ.lift _) (liftEq _ e)) (ir (hσ.lift _) (hυ.lift _) (liftEq _ e))
  | abort ha ih => exact abort_congr (ha.subst hσ) (ha.subst hυ) (ih hσ hυ e)

theorem let_beta_branch (h : Tm.BranchValue Γ a A) (k : Typed (A :: Γ) b B) :
    ReturnEq Γ (.let₁ a b) (b.subst (Tm.singleSubst a)) B :=
  (split_let h.hasType k).trans (.paper (.cfgEta (.native
    (.letValue h (UnaryReturn.returnOnce_valueBranches k).hasType))))

theorem let₂_beta_branch {c : Tm Φ} (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B)
    (hk : Typed (B :: A :: Γ) c D) :
    ReturnEq Γ (.let₂ (.pair a b) c) (c.subst (Tm.consSubst b (Tm.singleSubst a))) D :=
  (operand (Continuation.split_let₂ (.pair ha.hasType hb.hasType) hk)).trans
    (.paper (.productBeta (.let₂Beta ha hb (UnaryReturn.returnOnce_valueBranches hk).hasType)))

/-- If the producer replays to a typed branch value, native value β and
substitution congruence give β at the original producer and body. -/
theorem let_beta_of_value (h : Typed Γ a A) (k : Typed (A :: Γ) b B)
    {c : Tm Φ} (hc : Tm.BranchValue Γ c A) (e : ReturnEq Γ a c A) :
    ReturnEq Γ (.let₁ a b) (b.subst (Tm.singleSubst a)) B := by
  have substEq : ∀ ⦃i T⦄, At (A :: Γ) i T → ReturnEq Γ (Tm.singleSubst c i) (Tm.singleSubst a i) T := by
    intro i T ht
    cases i with
    | zero =>
      cases Option.some.inj ht
      exact e.symm
    | succ i => exact return_refl (.var ht)
  exact (let_congr h hc.hasType k k e (return_refl k)).trans
    ((let_beta_branch hc k).trans (subst_return k (Tm.Subst.HasType.single hc.hasType) (Tm.Subst.HasType.single h) substEq))

theorem erase_instantiate_single {n : Nat} (a : CaseTm Φ n) (b : CaseTm Φ (n + 1)) :
    erase (b.instantiate a) = (erase b).subst (Tm.singleSubst (erase a)) := by
  rw [Morphism.CaseSSA.erase_instantiate]
  congr 1
  funext i
  cases i <;> rfl

private theorem let_beta_value {n : Nat} {β : BoundCtx (Ty α) n} {a : CaseTm Φ n}
    {b : CaseTm Φ (n + 1)} (ha : Tm.BranchValue β.toList (erase a) A)
    (hb : CaseType Φ Γ₀ (β.snoc A) b B) :
    ReturnEq β.toList (erase (.let₁ a b)) (erase (b.instantiate a)) B := by
  rw [erase_instantiate_single]
  exact let_beta_branch ha (erase_hasType hb)

private theorem let_beta (beta : PureLetBetaReplay (Ψ := Φ) (α := α) pe)
    {n : Nat} {β : BoundCtx (Ty α) n} {a : CaseTm Φ n} {b : CaseTm Φ (n + 1)}
    (pure : LetCase.LocallyNameless.Pure pe a)
    (ha : CaseType Φ Γ₀ β a A) (hb : CaseType Φ Γ₀ (β.snoc A) b B) :
    ReturnEq β.toList (erase (.let₁ a b)) (erase (b.instantiate a)) B := by
  classical
  by_cases value : Tm.BranchValue β.toList (erase a) A
  · exact let_beta_value value hb
  · exact beta pure ha hb value

private theorem core (beta : PureLetBetaReplay (Ψ := Φ) (α := α) pe)
    {n : Nat} {β : BoundCtx (Ty α) n} {a b : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty α}
    (root : CoreAxiom pe a b) (ha : CaseType Φ Γ₀ β a A) (hb : CaseType Φ Γ₀ β b A) :
    ReturnEq β.toList (erase a) (erase b) A := by
  cases root with
  | sequencing h =>
    cases h with
    | bindOp a c =>
      cases ha with
      | let₁ h hc =>
        cases h with
        | op ha =>
          simpa only [erase, erase_under, Fin.val_zero] using bind_op _ (erase_hasType ha) (erase_hasType hc)
    | bindLet a b c =>
      cases ha with
      | let₁ h hc =>
        cases h with
        | let₁ ha hb =>
          simpa only [erase, erase_under, Fin.val_zero] using bind_let (erase_hasType ha) (erase_hasType hb) (erase_hasType hc)
    | bindLetPair a b c =>
      cases ha with
      | let₁ h hc =>
        cases h with
        | let₂ ha hb =>
          simpa only [erase, erase_under, Fin.val_zero] using bind_let_pair (erase_hasType ha) (erase_hasType hb) (erase_hasType hc)
    | bindLetCase e l r k =>
      cases ha with
      | let₁ h hk =>
        cases h with
        | case he hl hr =>
          simpa only [erase, erase_under, Fin.val_zero] using
            bind_let_case (erase_hasType he) (erase_hasType hl) (erase_hasType hr) (erase_hasType hk)
    | bindPair a b =>
      cases ha with
      | let₂ ha hb =>
        simpa only [erase, erase_under₂, Fin.val_zero] using bind_pair (erase_hasType ha) (erase_hasType hb)
    | bindCase a l r =>
      cases ha with
      | case ha hl hr =>
        simpa only [erase, erase_under, Fin.val_zero] using bind_case (erase_hasType ha) (erase_hasType hl) (erase_hasType hr)
  | structural h =>
    cases h with
    | letEta _ => exact let_eta (erase_hasType hb)
    | caseBetaL _ _ _ =>
      cases ha with
      | case he hl hr =>
        cases he with
        | inl he => exact case_beta_left (erase_hasType he) (erase_hasType hl) (erase_hasType hr)
    | caseBetaR _ _ _ =>
      cases ha with
      | case he hl hr =>
        cases he with
        | inr he => exact case_beta_right (erase_hasType he) (erase_hasType hl) (erase_hasType hr)
    | letBeta pure =>
      cases ha with
      | let₁ ha hb => exact let_beta beta pure ha hb
    | unitEta _ =>
      cases ha with
      | let₁ _ body =>
        cases body
        exact unit_eta (erase_hasType hb)
    | pairBeta _ _ _ =>
      cases ha with
      | let₂ h hc =>
        cases h with
        | pair ha hb =>
          simpa only [erase, Morphism.CaseSSA.erase_lift] using
            pair_beta (pe := pe) (erase_hasType ha) (erase_hasType hb) (erase_hasType hc)
    | pairEta _ =>
      cases ha with
      | let₂ ha body =>
        cases body with
        | pair l r =>
          cases l
          cases r
          exact pair_eta (erase_hasType ha)
    | caseEta _ =>
      cases ha with
      | case scr l r =>
        cases l with
        | inl l =>
          cases r with
          | inr r =>
            cases l
            cases r
            exact case_eta (pe := pe) (erase_hasType scr)
    | emptyInitial _ _ _ =>
      cases ha with
      | let₁ h hb' =>
        cases h with
        | abort ha =>
          cases hb with
          | let₁ _ hc' => exact empty_initial (erase_hasType ha) (erase_hasType hb') (erase_hasType hc')

theorem return_equiv_proof (beta : PureLetBetaReplay (Ψ := Φ) (α := α) pe)
    {n : Nat} {β : BoundCtx (Ty α) n} {a b : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty α}
    (h : Equiv pe Γ₀ β a b A) : ReturnEq β.toList (erase a) (erase b) A := by
  induction h with
  | refl h => exact return_refl (erase_hasType h)
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | unit => exact return_refl .unit
  | ax root ha hb => exact core beta root ha hb
  | op h ih => exact op_congr _ (erase_hasType h.hasType.1) (erase_hasType h.hasType.2) ih
  | let₁ h k ih ik =>
    exact let_congr (erase_hasType h.hasType.1) (erase_hasType h.hasType.2)
      (erase_hasType k.hasType.1) (erase_hasType k.hasType.2) ih ik
  | let₂ h k ih ik =>
    exact let₂_congr (erase_hasType h.hasType.1) (erase_hasType h.hasType.2)
      (erase_hasType k.hasType.1) (erase_hasType k.hasType.2) ih ik
  | pair h k ih ik =>
    exact pair_congr (erase_hasType h.hasType.1) (erase_hasType h.hasType.2)
      (erase_hasType k.hasType.1) (erase_hasType k.hasType.2) ih ik
  | inl h ih => exact inl_congr (erase_hasType h.hasType.1) (erase_hasType h.hasType.2) ih
  | inr h ih => exact inr_congr (erase_hasType h.hasType.1) (erase_hasType h.hasType.2) ih
  | case h l r ih il ir =>
    exact case_congr (erase_hasType h.hasType.1) (erase_hasType h.hasType.2)
      (erase_hasType l.hasType.1) (erase_hasType l.hasType.2) (erase_hasType r.hasType.1) (erase_hasType r.hasType.2) ih il ir
  | abort h ih => exact abort_congr (erase_hasType h.hasType.1) (erase_hasType h.hasType.2) ih

private theorem admitted (t : Tm Φ) : Recursive.Admitted t := by induction t <;> simp_all [Recursive.Admitted]

private theorem returned_to_reified {n : Nat} {β : BoundCtx (Ty α) n}
    {a : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty α} (d : Derivation Φ Γ₀ β a A) :
    ReplayEqv pe β.toList (returnOnce (erase a)) ((Code.ofLetCase d).guardedSSA 0) [A] := by
  obtain ⟨_, _, _, original, reified⟩ := Recursive.normalize (pe := pe) (rfl : At [A] 0 A)
    ⟨a, d⟩ (admitted (erase a))
  exact operand (original.trans reified.symm)

theorem reify_equiv_proof (beta : PureLetBetaReplay (Ψ := Φ) (α := α) pe)
    {n : Nat} {β : BoundCtx (Ty α) n} {a b : LetCase.LocallyNameless.Tm Empty Φ n} {A : Ty α}
    (da : Derivation Φ Γ₀ β a A) (db : Derivation Φ Γ₀ β b A) (h : Equiv pe Γ₀ β a b A) :
    ReplayEqv pe β.toList ((Code.ofLetCase da).guardedSSA 0) ((Code.ofLetCase db).guardedSSA 0) [A] :=
  (returned_to_reified da).symm.trans ((return_equiv_proof beta h).trans (returned_to_reified db))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
