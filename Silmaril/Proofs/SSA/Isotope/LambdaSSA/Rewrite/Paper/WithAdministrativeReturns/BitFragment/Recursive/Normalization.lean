module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.Syntax
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Replay.Thms

/-! # Native normalization by structural recursion on the original source -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.BitFragment.Recursive
open Paper.WithCaseBind.BitQuery (signature)
open Paper.WithCaseBind.BitQuery.RequestTree (drop_weakening)
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (Live slots)
open Paper.RetainedLet (returnOnce)
open Paper.UnaryReturn (returnOnce_valueBranches)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.DeBruijn (lift)

local notation "U" => (Ty.unit : Ty Empty)

private theorem beta {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {A : Ty Empty}
    {a : Tm signature.Instr} {b : Region signature.Instr}
    (ha : Tm.BranchValue Γ a A) (hb : HasType (A :: Γ) b L) :
    Eqv false Γ (.let₁ a b) (b.substVars (Tm.singleSubst a)) L :=
  .paper (.cfgEta (.native (.letValue ha hb)))

private theorem seqOnce {Γ : VCtx (Ty Empty)} {A : Ty Empty} {a b : Tm signature.Instr}
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b Bit) :
    Eqv false Γ (returnOnce (.let₁ a b)) (.let₁ a (returnOnce b)) [Bit] :=
  let₁_let₁ false ha hb (.br (ℓ := 0) rfl (.var (i := 0) rfl))

set_option backward.isDefEq.respectTransparency false in
private theorem term_to_region {k n : Nat} (c : Code k n) :
    k = 1 → ∀ {m : Nat} (ρ : Fin n → Fin m),
      Eqv false (Live m) (returnOnce (c.term ρ)) (c.region ρ) [Bit] := by
  induction c with
  | ret out i =>
    intro one m ρ
    have zero : out.val = 0 := by have := out.isLt; omega
    have e : Eqv false (Live m) (returnOnce (.var (ρ i).val))
        (.br 0 (.var (ρ i).val)) [Bit] :=
      beta (.var ((slots m).typed (ρ i))) (.br (ℓ := 0) rfl (.var (i := 0) rfl))
    simpa only [Code.term, Code.region, zero] using e
  | letUnit b ih =>
    intro one m ρ
    let wk := Ren.wk (Live m) U
    have bound := seqOnce (.unit : Tm.HasType (Live m) (.unit : Tm signature.Instr) U)
      ((term_typed b ρ).rename wk)
    exact bound.trans (.let₁ .unit ((ih one ρ).renameVars wk))
  | letBit a b _ ih =>
    intro one m ρ
    exact (seqOnce (term_typed a ρ) (term_typed b (push ρ))).trans
      (.let₁ (term_typed a ρ) (ih one (push ρ)))
  | ask label q l r il ir =>
    intro one m ρ
    have e : Eqv false (Live m) (returnOnce (.case (request label (q.map ρ))
        (l.term (push ρ)) (r.term (push ρ))))
        (.case (request label (q.map ρ)) (returnOnce (l.term (push ρ))) (returnOnce (r.term (push ρ)))) [Bit] :=
      let₁_case false (request_typed label (q.map ρ)) (term_typed l (push ρ)) (term_typed r (push ρ))
        (.br (ℓ := 0) rfl (.var (i := 0) rfl))
    exact e.trans (.case (request_typed label (q.map ρ)) (il one (push ρ)) (ir one (push ρ)))

private def select (i : Nat) : Nat → Nat
  | 0 => i
  | j + 1 => j

private theorem substitute_result {k n m : Nat} (b : Code k (n + 1)) (ρ : Fin n → Fin m) (i : Fin m) :
    (b.region (push ρ)).substVars (Tm.singleSubst (.var i.val)) = b.region (Fin.cases i ρ) := by
  have sub : Tm.singleSubst (.var i.val : Tm signature.Instr) = Tm.var ∘ select i.val := by
    funext j
    cases j <;> rfl
  rw [sub, ← Region.renameVars_eq_substVars]
  apply region_rename
  exact Fin.cases rfl (fun _ => rfl)

private theorem lift_body {k n m : Nat} (b : Code k (n + 1)) (ρ : Fin n → Fin m) :
    liftLSubstVars (fun _ => b.region (push ρ)) = fun _ => b.region (push (Fin.succ ∘ ρ)) := by
  funext j
  apply region_rename
  exact Fin.cases rfl (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem bind_replay {k n m : Nat} (t : Normal 1 m) (b : Code k (n + 1))
    (ρ : Fin n → Fin m)
    (body : ∀ (p : Nat) (σ : Fin (n + 1) → Fin p),
      Eqv false (Live p) (b.region σ) (b.normalize σ).region (Live k)) :
    Eqv false (Live m) (t.region.lsubst (fun _ => b.region (push ρ)))
      (t.bind (fun _ captures payload => b.normalize (Fin.cases payload (captures ∘ ρ)))).region (Live k) := by
  induction t with
  | ret _ i =>
    change Eqv false _ ((b.region (push ρ)).substVars (Tm.singleSubst (.var i.val))) _ _
    rw [substitute_result]
    exact body _ (Fin.cases i ρ)
  | ask label i l r il ir =>
    simp only [Normal.region, Normal.bind, Region.lsubst, lift_body]
    exact .case (request_typed label (.read i)) (il (Fin.succ ∘ ρ)) (ir (Fin.succ ∘ ρ))

private theorem post_returnOnce (a : Tm signature.Instr) (k : Region signature.Instr) :
    (returnOnce a).lsubst (fun _ => k) = .let₁ a k :=
  lsubst_bindBranchArguments_br 0 a (fun _ => k)

set_option backward.isDefEq.respectTransparency false in
private theorem request_beta {m k : Nat} (label : Bool) (q : Query m)
    {l r : Region signature.Instr} (hl : ValueBranches (Bit :: Live m) l (Live k))
    (hr : ValueBranches (Bit :: Live m) r (Live k)) :
    Eqv false (Live m) (.case (request label q) l r) (.case (request label (.read q.slot)) l r) (Live k) := by
  cases q with
  | read i => exact .refl (.case (request_typed label (.read i)) hl.hasType hr.hasType)
  | known tag i dead =>
    let op : signature.Instr := .ask label
    let payload : Tm.BranchValue (Live m) (.var i.val : Tm signature.Instr) Bit :=
      .var ((slots m).typed i)
    let picked : Tm.HasType (Bit :: Live m) (.var 0 : Tm signature.Instr) Bit :=
      .var (i := 0) rfl
    let other : Tm.HasType (Bit :: Live m) (.var (dead.val + 1) : Tm signature.Instr) Bit :=
      .var ((slots m).typed dead)
    cases tag
    · exact ofConstructorOperands false
        (Paper.WithConstructorCaseOperands.Step.caseCall op (.left payload picked other) rfl hl hr).replay
    · exact ofConstructorOperands false
        (Paper.WithConstructorCaseOperands.Step.caseCall op (.right payload other picked) rfl hl hr).replay

set_option backward.isDefEq.respectTransparency false in
theorem replay {k n m : Nat} (c : Code k n) (ρ : Fin n → Fin m) :
    Eqv false (Live m) (c.region ρ) (c.normalize ρ).region (Live k) := by
  induction c generalizing m with
  | ret out i => exact .refl (region_typed (.ret out i) ρ).hasType
  | letUnit b ih =>
    have drop := beta Tm.BranchValue.unit
      ((region_typed b ρ).renameVars (Ren.wk (Live m) U)).hasType
    rw [drop_weakening] at drop
    exact drop.trans (ih ρ)
  | @letBit exits _ a b ia ib =>
    have norm := (term_to_region a rfl ρ).trans (ia ρ)
    have typed : LSubst.HasType (Live m) [Bit] (Live exits) (fun _ => b.region (push ρ)) :=
      fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ (region_typed b (push ρ)).hasType
    have post := Paper.Extension.Eqv.lsubstPost norm (returnOnce_valueBranches (term_typed a ρ))
      (normal_typed (a.normalize ρ)) typed
    rw [post_returnOnce] at post
    exact post.trans (bind_replay (a.normalize ρ) b ρ (fun _ σ => ib σ))
  | ask label q l r il ir =>
    have same : (q.map ρ).slot = ρ q.slot := by cases q <;> rfl
    have e := request_beta label (q.map ρ) (region_typed l (push ρ)) (region_typed r (push ρ))
    rw [same] at e
    exact e.trans (.case (request_typed label (.read (ρ q.slot))) (il (push ρ)) (ir (push ρ)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive
