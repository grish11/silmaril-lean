module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.PacketCases.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms

/-! # Native case extensionality at a finite retained reply packet -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PacketCases

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper
open Paper.WithCaseBind.OpenReplay

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "E" => Paper.Extension.Eqv Seed
local notation "U" => (unit : Ty Empty)

theorem bit_case_ext {Γ L : List (Ty Empty)} {p q : Region signature.Instr} {i : Nat}
    (hi : At Γ i Bit) (hp : HasType Γ p L) (hq : HasType Γ q L)
    (arms : ∀ b, E (U :: Γ) (p.substVars (bitBranch i b)) (q.substVars (bitBranch i b)) L) :
    E Γ p q L := by
  let ρ (j : Nat) := if j = i then 0 else j + 1
  have hρ : Ren Γ (Bit :: Γ) ρ := by
    intro j D hj
    by_cases e : j = i
    · subst j
      have t := Option.some.inj (hj.symm.trans hi)
      subst D
      simp [ρ, At]
    · simpa [ρ, e, At] using hj
  have identity (r : Region signature.Instr) :
      (r.renameVars ρ).substVars (Tm.singleSubst (.var i)) = r := by
    rw [substVars_renameVars]
    have eq : (Tm.singleSubst (.var i) ∘ ρ) = (Tm.var : Nat → Tm signature.Instr) := by
      funext j
      by_cases e : j = i
      · subst j; simp [ρ, Tm.singleSubst, Tm.consSubst]
      · simp [ρ, e, Tm.singleSubst, Tm.consSubst]
    rw [eq, substVars_var]
  have branch (r : Region signature.Instr) (b : Bool) :
      (r.renameVars ρ).substVars (Tm.replaceNewest (replyBitTag b (.var 0))) =
        r.substVars (bitBranch i b) := by
    rw [substVars_renameVars]
    congr
    funext j
    by_cases e : j = i <;> simp [ρ, bitBranch, e, Tm.replaceNewest, Tm.consSubst]
  have expand (r : Region signature.Instr) (hr : HasType Γ r L) :
      E Γ (.case (.var i) (r.substVars (bitBranch i false)) (r.substVars (bitBranch i true))) r L := by
    have step := Paper.Extension.Eqv.paper (Seed := Seed) (.cfgEta (.native
      (.caseValue (.var hi) (hr.renameVars hρ))))
    rw [identity] at step
    rw [← branch r false, ← branch r true]
    exact step
  exact (expand p hp).symm.trans ((Paper.Extension.Eqv.case (.var hi) (arms false) (arms true)).trans (expand q hq))

theorem product_case_ext {Γ L : List (Ty Empty)} {p q : Region signature.Instr} {i : Nat}
    {A B : Ty Empty} (hi : At Γ i (product A B)) (hp : HasType Γ p L) (hq : HasType Γ q L)
    (pair : E (B :: A :: Γ) (p.substVars (splitProduct i)) (q.substVars (splitProduct i)) L) :
    E Γ p q L :=
  (Paper.Extension.Eqv.paper (product_variable_eta_context hi hp)).symm.trans
    ((Paper.Extension.Eqv.let₂ (.var hi) pair).trans (.paper (product_variable_eta_context hi hq)))

theorem splitProduct_values {Γ : List (Ty Empty)} {i : Nat} {A B : Ty Empty}
    (hi : At Γ i (product A B)) :
    ∀ ⦃j D⦄, At Γ j D → Tm.BranchValue (Φ := signature.Instr) (B :: A :: Γ) (splitProduct i j) D := by
  intro j D hj
  by_cases e : j = i
  · subst j
    have t := Option.some.inj (hj.symm.trans hi)
    subst D
    simp only [splitProduct, ↓reduceIte]
    exact .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  · simp only [splitProduct, e, ↓reduceIte]
    exact .var (by simpa [At] using hj)

theorem bitBranch_values {Γ : List (Ty Empty)} {i : Nat} (hi : At Γ i Bit) (b : Bool) :
    ∀ ⦃j D⦄, At Γ j D → Tm.BranchValue (U :: Γ) (bitBranch i b j) D := by
  intro j D hj
  by_cases e : j = i
  · subst j
    have t := Option.some.inj (hj.symm.trans hi)
    subst D
    simp only [bitBranch, ↓reduceIte]
    cases b <;> simp only [replyBitTag, Bool.false_eq_true, ↓reduceIte]
    · exact .inl (.var (i := 0) rfl)
    · exact .inr (.var (i := 0) rfl)
  · simp only [bitBranch, e, ↓reduceIte]
    exact .var (by simpa [At] using hj)

private theorem typeSplit {Γ : List (Ty Empty)} {i : Nat} {A B : Ty Empty}
    (hi : At Γ i (product A B)) :
    Tm.Subst.HasType (Φ := signature.Instr) Γ (B :: A :: Γ) (splitProduct i) :=
  fun _ _ hj => (splitProduct_values hi hj).hasType

private theorem typeBranch {Γ : List (Ty Empty)} {i : Nat} (hi : At Γ i Bit) (b : Bool) :
    Tm.Subst.HasType (Φ := signature.Instr) Γ (U :: Γ) (bitBranch i b) :=
  fun _ _ hj => (bitBranch_values hi b hj).hasType

private def expandSubst : (n i : Nat) → Finite.Assignment n → Nat → Tm signature.Instr
  | 0, _, _ => Tm.var
  | n + 1, i, env => fun j =>
    (((splitProduct i j).subst (bitBranch 0 (env 0))).subst (expandSubst n 2 env.tail))

private theorem expand_other (n i : Nat) (env : Finite.Assignment n)
    (j : Nat) (other : j ≠ i) :
    expandSubst n i env j = .var (j + 3 * n) := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih =>
    simp only [expandSubst, splitProduct, other, ↓reduceIte, Tm.subst]
    have neq : j + 2 ≠ 0 := by omega
    simp only [bitBranch, neq, ↓reduceIte]
    change expandSubst n 2 env.tail (j + 2 + 1) = _
    rw [ih 2 env.tail (j + 2 + 1) (by omega)]
    congr 1
    omega

private theorem tag_subst (b : Bool) (u : Tm signature.Instr) (σ : Nat → Tm signature.Instr) :
    (replyBitTag b u).subst σ = replyBitTag b (u.subst σ) := by
  cases b <;> rfl

private theorem expand_focused (n i : Nat) (env : Finite.Assignment n) :
    expandSubst n i env i = casePacket env i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    change (((splitProduct i i).subst (bitBranch 0 (env 0))).subst
      (expandSubst n 2 env.tail)) = _
    simp only [splitProduct, ↓reduceIte, Tm.subst, bitBranch, Nat.one_ne_zero, tag_subst]
    rw [ih 2 env.tail, expand_other n 2 env.tail 0 (by decide)]
    have base : packetBase n 2 = .var (2 : Nat) := by cases n <;> rfl
    change Tm.pair (replyPacket env.tail (packetPayload n) (packetBase n 2))
      (replyBitTag (env 0) (.var (0 + 3 * n))) = _
    rw [base]
    cases h : env 0 <;> simp only [casePacket, replyPacket, packetBase, replyBitTag, h,
      Bool.false_eq_true, ↓reduceIte, packetPayload, Fin.cases_zero, Fin.cases_succ, Nat.zero_add]

private theorem packet_ext_at {Γ L : List (Ty Empty)} {p q : Region signature.Instr} {i n : Nat}
    (hi : At Γ i (replyContext n)) (hp : HasType Γ p L) (hq : HasType Γ q L)
    (rows : ∀ env, E (packetCaseCtx n Γ)
      (p.substVars (expandSubst n i env))
      (q.substVars (expandSubst n i env)) L) :
    E Γ p q L := by
  induction n generalizing Γ p q i with
  | zero =>
    have base := rows (Fin.elim0 : Finite.Assignment 0)
    simpa only [packetCaseCtx, expandSubst, substVars_var] using base
  | succ n ih =>
    apply product_case_ext hi hp hq
    let pp := hp.substVars (typeSplit hi)
    let qq := hq.substVars (typeSplit hi)
    have hBit : At (Bit :: replyContext n :: Γ) 0 Bit := rfl
    apply bit_case_ext hBit pp qq
    intro b
    have hOlder : At (U :: Bit :: replyContext n :: Γ) 2 (replyContext n) := rfl
    apply ih hOlder (pp.substVars (typeBranch hBit b)) (qq.substVars (typeBranch hBit b))
    intro env
    simp only [substVars_comp]
    exact rows (env.push b)

theorem packet_case_ext {n : Nat} {L : List (Ty Empty)} {p q : Region signature.Instr}
    (hp : HasType [replyContext n] p L) (hq : HasType [replyContext n] q L)
    (rows : ∀ env : Finite.Assignment n, E (packetCaseCtx n [replyContext n])
      (p.substVars (Tm.singleSubst (casePacket env 0)))
      (q.substVars (Tm.singleSubst (casePacket env 0))) L) :
    E [replyContext n] p q L := by
  apply packet_ext_at (i := 0) rfl hp hq
  intro env
  rw [Paper.SingletonReification.SingleCfg.singleton_subst hp
      (υ := Tm.singleSubst (casePacket env 0)) (expand_focused n 0 env),
    Paper.SingletonReification.SingleCfg.singleton_subst hq
      (υ := Tm.singleSubst (casePacket env 0)) (expand_focused n 0 env)]
  exact rows env

private theorem caseCtx_shift {Γ : List (Ty Empty)} {i : Nat} {A : Ty Empty}
    (n : Nat) (hi : At Γ i A) : At (packetCaseCtx n Γ) (i + 3 * n) A := by
  induction n generalizing Γ i with
  | zero => simpa [packetCaseCtx] using hi
  | succ n ih =>
    have h : At (U :: Bit :: replyContext n :: Γ) (i + 3) A := by
      simpa [At] using hi
    have shift := ih h
    change At (packetCaseCtx n (U :: Bit :: replyContext n :: Γ)) (i + 3 * (n + 1)) A
    rw [show i + 3 * (n + 1) = i + 3 + 3 * n by omega]
    exact shift

theorem packetPayload_typed {Γ : List (Ty Empty)} (n : Nat) (j : Fin n) :
    Tm.BranchValue (packetCaseCtx n Γ) (packetPayload n j) U := by
  induction n generalizing Γ with
  | zero => exact j.elim0
  | succ n ih =>
    cases j using Fin.cases with
    | zero =>
      have h : At (U :: Bit :: replyContext n :: Γ) 0 U := rfl
      have hShift := caseCtx_shift n h
      rw [Nat.zero_add] at hShift
      exact .var hShift
    | succ j => exact ih j

theorem packetBase_typed {Γ : List (Ty Empty)} {i n : Nat}
    (hi : At Γ i (replyContext n)) : Tm.BranchValue (packetCaseCtx n Γ) (packetBase n i) U := by
  induction n generalizing Γ i with
  | zero => exact .var hi
  | succ n ih =>
    have h : At (U :: Bit :: replyContext n :: Γ) 2 (replyContext n) := rfl
    have inner := ih h
    have base : packetBase n 2 = .var 2 := by cases n <;> rfl
    rw [base] at inner
    exact inner


end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PacketCases
