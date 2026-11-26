module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Defs

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

/-! # Replay under finite typed query and reply contexts -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryQuotation

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.RequestTree
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Assignment)

local notation "U" => (Ty.unit : Ty Empty)
local notation "E" => Paper.Extension.Eqv Seed

theorem drop_weakening (r : Region signature.Instr) (a : Tm signature.Instr) :
    (r.renameVars Nat.succ).substVars (Tm.singleSubst a) = r := by
  rw [substVars_renameVars]
  exact substVars_var r

private theorem weaken_subst_term (a : Tm signature.Instr) (σ : Nat → Tm signature.Instr) :
    (a.rename Nat.succ).subst (Tm.liftSubst σ) = (a.subst σ).rename Nat.succ := by
  rw [Tm.subst_rename, Tm.rename_subst]
  rfl

private theorem weaken_subst_region (r : Region signature.Instr) (σ : Nat → Tm signature.Instr) :
    (r.renameVars Nat.succ).substVars (Tm.liftSubst σ) = (r.substVars σ).renameVars Nat.succ := by
  rw [substVars_renameVars, renameVars_substVars]
  rfl

private theorem choose_subst {n : Nat} (e : Expr n) (slots : Fin n → Tm signature.Instr)
    (l r : Region signature.Instr) (σ : Nat → Tm signature.Instr) :
    (choose e slots l r).substVars σ = choose e (fun i => (slots i).subst σ) (l.substVars σ) (r.substVars σ) := by
  induction e generalizing l r σ with
  | literal b => cases b <;> rfl
  | read i => simp only [choose, Region.substVars, weaken_subst_region]
  | split lo hi ihl ihr =>
    simp only [choose, Region.substVars, ihl, ihr, weaken_subst_region, weaken_subst_term]

private theorem constructor_subst (b : Bool) (a : Tm signature.Instr) (σ : Nat → Tm signature.Instr) :
    (constructorBit b a).subst σ = constructorBit b (a.subst σ) := by
  cases b <;> rfl

private theorem constructor_weaken (b : Bool) (a : Tm signature.Instr) :
    (constructorBit b a).rename Nat.succ = constructorBit b (a.rename Nat.succ) := by
  cases b <;> rfl

private theorem select_case {Γ L : List (Ty Empty)} {a : Tm signature.Instr} {l r : Region signature.Instr}
    (b : Bool) (ha : Tm.HasType Γ a U)
    (hl : ValueBranches (U :: Γ) l L) (hr : ValueBranches (U :: Γ) r L) :
    E Γ (.case (constructorBit b a) l r) (.let₁ a (if b then r else l)) L := by
  cases b
  · exact .paper (.cfgEta (.native (.base (.caseInl ha hl.hasType hr.hasType))))
  · exact .paper (.cfgEta (.native (.base (.caseInr ha hl.hasType hr.hasType))))

private theorem erase_binder {Γ L : List (Ty Empty)} {a : Tm signature.Instr} {r : Region signature.Instr}
    (ha : Tm.BranchValue Γ a U) (hr : ValueBranches Γ r L) :
    E Γ (.let₁ a (r.renameVars Nat.succ)) r L := by
  have h := Paper.Extension.Eqv.paper (Seed := Seed)
    (.cfgEta (.native (.letValue ha (hr.renameVars (Ren.wk Γ U)).hasType)))
  rwa [drop_weakening] at h

private theorem choose_known {n : Nat} (e : Expr n) (env : Assignment n)
    {Γ L : List (Ty Empty)} (payload : Fin n → Tm signature.Instr)
    (hp : ∀ i, Tm.BranchValue Γ (payload i) U)
    {l r : Region signature.Instr} (hl : ValueBranches Γ l L) (hr : ValueBranches Γ r L) :
    E Γ (choose e (fun i => constructorBit (env i) (payload i)) l r)
      (if e.eval env then r else l) L := by
  induction e generalizing Γ l r with
  | literal b =>
    cases b
    · exact .refl hl.hasType
    · exact .refl hr.hasType
  | read i =>
    refine (select_case (env i) (hp i).hasType (hl.renameVars (Ren.wk Γ U))
      (hr.renameVars (Ren.wk Γ U))).trans ?_
    cases eq : env i
    · simp only [Expr.eval, eq, Bool.false_eq_true, ite_false]
      exact erase_binder (hp i) hl
    · simp only [Expr.eval, eq, ite_true]
      exact erase_binder (hp i) hr
  | @split n lo hi ihl ihr =>
    let older := fun (i : Fin n) => (payload i.succ).rename Nat.succ
    have ht (i) : Tm.BranchValue (U :: Γ) (older i) U := by
      unfold older
      rw [Tm.rename_eq_subst]
      exact (hp i.succ).subst (fun _ _ h => .var (Ren.wk Γ U h))
    have hbit (i) : Tm.HasType (U :: Γ) (constructorBit (env.tail i) (older i)) Bit :=
      (constructorBit_value _ (ht i)).hasType
    let wl := hl.renameVars (Ren.wk Γ U)
    let wr := hr.renameVars (Ren.wk Γ U)
    simp only [choose, constructor_weaken]
    refine (select_case (env 0) (hp 0).hasType (choose_typed lo hbit wl wr)
      (choose_typed hi hbit wl wr)).trans ?_
    cases h : env 0
    · simp only [Expr.eval, h, Bool.false_eq_true, ite_false]
      refine (Paper.Extension.Eqv.let₁ (hp 0).hasType (ihl env.tail older ht wl wr)).trans ?_
      cases lo.eval env.tail
      · exact erase_binder (hp 0) hl
      · exact erase_binder (hp 0) hr
    · simp only [Expr.eval, h, ite_true]
      refine (Paper.Extension.Eqv.let₁ (hp 0).hasType (ihr env.tail older ht wl wr)).trans ?_
      cases hi.eval env.tail
      · exact erase_binder (hp 0) hl
      · exact erase_binder (hp 0) hr

/-- A case expansion at any typed live coordinate retains all other slots. -/
theorem expand_bit {Γ L : List (Ty Empty)} {r : Region signature.Instr} {i : Nat}
    (hi : At Γ i Bit) (hr : HasType Γ r L) :
    E Γ (.case (.var i) (r.substVars (focus i false)) (r.substVars (focus i true))) r L := by
  let ρ (j : Nat) := if j = i then 0 else j + 1
  have hρ : Ren Γ (Bit :: Γ) ρ := by
    intro j A hj
    by_cases e : j = i
    · subst j
      cases Option.some.inj (hj.symm.trans hi)
      simp [ρ, At]
    · simpa [ρ, e, At] using hj
  have identity : (r.renameVars ρ).substVars (Tm.singleSubst (.var i)) = r := by
    rw [substVars_renameVars]
    have eq : (Tm.singleSubst (.var i) ∘ ρ) = (Tm.var : Nat → Tm signature.Instr) := by
      funext j
      by_cases e : j = i
      · subst j; simp [ρ, Tm.singleSubst, Tm.consSubst]
      · simp [ρ, e, Tm.singleSubst, Tm.consSubst]
    rw [eq, substVars_var]
  have branch (b : Bool) :
      (r.renameVars ρ).substVars (Tm.replaceNewest (constructorBit b (.var 0))) =
        r.substVars (focus i b) := by
    rw [substVars_renameVars]
    congr
    funext j
    by_cases e : j = i <;> simp [ρ, focus, e, Tm.replaceNewest, Tm.consSubst]
  have step := Paper.Extension.Eqv.paper (Seed := Seed) (.cfgEta (.native
    (.caseValue (.var hi) (hr.renameVars hρ))))
  rw [identity] at step
  erw [branch false, branch true] at step
  exact step

private def rowCtx (n : Nat) (Γ : List (Ty Empty)) : List (Ty Empty) :=
  List.replicate n U ++ Γ

private theorem rowCtx_succ (n : Nat) (Γ : List (Ty Empty)) :
    rowCtx (n + 1) Γ = rowCtx n (U :: Γ) := by
  simp [rowCtx, List.replicate_succ', List.append_assoc]

/-- Split each physical slot once. Each focus retains the rest of the context. -/
private def rowSubst : {n : Nat} → (Fin n → Nat) → Assignment n → Nat → Tm signature.Instr
  | 0, _, _ => Tm.var
  | _ + 1, slots, env => fun j => (focus (slots 0) (env 0) j).subst
      (rowSubst (fun i => (slots i.succ).succ) env.tail)

private theorem row_subst_typed {n : Nat} (env : Assignment n) {Γ : List (Ty Empty)} {slots : Fin n → Nat}
    (typed : ∀ i, At Γ (slots i) Bit) {i : Nat} {A : Ty Empty} (hi : At Γ i A) :
    Tm.BranchValue (rowCtx n Γ) (rowSubst slots env i) A := by
  induction n generalizing Γ i A with
  | zero => exact .var hi
  | succ n ih =>
    rw [rowCtx_succ]
    exact (focus_typed (typed 0) (env 0) hi).subst
      (fun _ _ h => ih env.tail (Γ := U :: Γ) (slots := fun j => (slots j.succ).succ)
        (fun j => typed j.succ) h)

private theorem row_outside {n : Nat} (slots : Fin n → Nat) (env : Assignment n) (i : Nat)
    (outside : ∀ j, slots j ≠ i) : rowSubst slots env i = .var (i + n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [rowSubst, focus, Ne.symm (outside 0), ite_false, Tm.subst]
    rw [ih (fun j => (slots j.succ).succ) env.tail i.succ
      (fun j eq => outside j.succ (Nat.succ.inj eq))]
    congr 1
    omega

private theorem row_focused {n : Nat} (slots : Fin n → Nat) (env : Assignment n) (i : Fin n)
    (distinct : Function.Injective slots) :
    rowSubst slots env (slots i) = constructorBit (env i) (.var (n - 1 - i.val)) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    let older := fun (j : Fin n) => (slots j.succ).succ
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [rowSubst, focus, ite_true, constructor_subst, Tm.subst, Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero]
      rw [row_outside older env.tail 0 (fun j => Nat.succ_ne_zero (slots j.succ))]
      rw [Nat.zero_add]
    · have different : slots j.succ ≠ slots 0 := fun h => Fin.succ_ne_zero j (distinct h)
      simp only [rowSubst, focus, different, ite_false, Tm.subst]
      have eq := ih older env.tail j (fun _ _ h => Fin.succ_inj.mp (distinct (Nat.succ.inj h)))
      rw [eq]
      congr 2
      simp only [Fin.val_succ]
      omega

/-- Newest-first binder indices run opposite the order in which the rows are expanded. -/
private theorem row_payload {Γ : List (Ty Empty)} {n : Nat} (i : Fin n) :
    Tm.BranchValue (Φ := signature.Instr) (rowCtx n Γ) (.var (n - 1 - i.val)) U := by
  apply Tm.BranchValue.var
  have inside : n - 1 - i.val < n := by omega
  have bound : n - 1 - i.val < (List.replicate n U).length := by simpa using inside
  rw [At, rowCtx, List.getElem?_append_left bound, List.getElem?_eq_getElem bound]
  simp

private theorem tail_push {n : Nat} (env : Assignment n) (b : Bool) :
    (env.push b).tail = env := by
  funext i
  simp [Assignment.tail, Assignment.push]

private theorem row_ext {n : Nat} {Γ L : List (Ty Empty)} {r s : Region signature.Instr}
    (slots : Fin n → Nat) (typed : ∀ i, At Γ (slots i) Bit) (hr : HasType Γ r L) (hs : HasType Γ s L)
    (rows : ∀ env : Assignment n, E (rowCtx n Γ) (r.substVars (rowSubst slots env))
      (s.substVars (rowSubst slots env)) L) : E Γ r s L := by
  induction n generalizing Γ r s with
  | zero => simpa only [rowCtx, List.replicate_zero, List.nil_append, rowSubst, substVars_var] using rows Fin.elim0
  | succ n ih =>
    have arm (b : Bool) : E (U :: Γ) (r.substVars (focus (slots 0) b))
        (s.substVars (focus (slots 0) b)) L := by
      apply ih (fun i => (slots i.succ).succ) (fun i => typed i.succ)
        (hr.substVars fun _ _ h => (focus_typed (typed 0) b h).hasType)
        (hs.substVars fun _ _ h => (focus_typed (typed 0) b h).hasType)
      intro env
      simp only [substVars_comp]
      simpa only [rowCtx_succ, rowSubst, tail_push, Assignment.push, Fin.cases_zero] using
        rows (env.push b)
    exact (expand_bit (typed 0) hr).symm.trans
      ((Paper.Extension.Eqv.case (.var (typed 0)) (arm false) (arm true)).trans (expand_bit (typed 0) hs))

theorem choose_eq {n : Nat} {Γ L : List (Ty Empty)} (slots : Slots Γ n) (e f : Expr n)
    {l r : Region signature.Instr} (hl : ValueBranches Γ l L) (hr : ValueBranches Γ r L)
    (equal : ∀ env, e.eval env = f.eval env) :
    E Γ (choose e slots.terms l r) (choose f slots.terms l r) L := by
  apply row_ext slots.index slots.typed (choose_typed e slots.term_typed hl hr).hasType
    (choose_typed f slots.term_typed hl hr).hasType
  intro env
  let σ := rowSubst slots.index env
  have typed : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue (rowCtx n Γ) (σ i) A :=
    fun _ _ h => row_subst_typed env slots.typed h
  have values : (fun i => (slots.terms i).subst σ) =
      fun i => constructorBit (env i) (.var (n - 1 - i.val)) :=
    funext fun i => row_focused slots.index env i slots.distinct
  change E _ ((choose e slots.terms l r).substVars σ) ((choose f slots.terms l r).substVars σ) L
  rw [choose_subst, choose_subst, values]
  have left := choose_known e env _ (fun i => row_payload i) (hl.substVars typed) (hr.substVars typed)
  have right := choose_known f env _ (fun i => row_payload i) (hl.substVars typed) (hr.substVars typed)
  rw [equal env] at left
  exact left.trans right.symm

theorem eqv_choose {n : Nat} {Γ L : List (Ty Empty)} (e : Expr n) {slots : Fin n → Tm signature.Instr}
    (typed : ∀ i, Tm.HasType Γ (slots i) Bit) {l r l' r' : Region signature.Instr}
    (hl : E Γ l l' L) (hr : E Γ r r' L) :
    E Γ (choose e slots l r) (choose e slots l' r') L := by
  induction e generalizing Γ l r l' r' with
  | literal b => cases b; exact hl; exact hr
  | read i => exact .case (typed i) (hl.renameVars (Ren.wk Γ U)) (hr.renameVars (Ren.wk Γ U))
  | split lo hi ihl ihr =>
    exact .case (typed 0)
      (ihl (fun i => (typed i.succ).rename (Ren.wk Γ U))
        (hl.renameVars (Ren.wk Γ U)) (hr.renameVars (Ren.wk Γ U)))
      (ihr (fun i => (typed i.succ).rename (Ren.wk Γ U))
        (hl.renameVars (Ren.wk Γ U)) (hr.renameVars (Ren.wk Γ U)))

theorem quote_choose {n : Nat} {Γ L : List (Ty Empty)} (slots : Slots Γ n) (e : Expr n)
    {l r : Region signature.Instr} (hl : ValueBranches Γ l L) (hr : ValueBranches Γ r L) :
    E Γ (choose e slots.terms l r) (choose (Expr.quote n e.eval) slots.terms l r) L :=
  choose_eq slots e (Expr.quote n e.eval) hl hr (fun env => (Expr.quote_eval n e.eval env).symm)

theorem region_replay {n : Nat} (t : Tree n) {Γ : VCtx (Ty Empty)} (slots : Slots Γ n) :
    E Γ (t.region slots) (t.key.region slots) Exits := by
  induction t generalizing Γ with
  | ret right i => exact .refl ((Tree.ret right i).typed slots).hasType
  | ask label query l r ihl ihr =>
    let left := l.key.typed slots.bind
    let right := r.key.typed slots.bind
    have step (b : Bool) : E Γ
        (requestRegion label b (l.region slots.bind) (r.region slots.bind))
        (requestRegion label b (l.key.region slots.bind) (r.key.region slots.bind)) Exits :=
      .case (.op (constructorBit_value b .unit).hasType) (ihl slots.bind) (ihr slots.bind)
    exact (eqv_choose query slots.term_typed (step false) (step true)).trans
      (quote_choose slots query (request_typed label false left right) (request_typed label true left right))

theorem packed_unguarded (t : Tree 1) :
    t.packed = Paper.Extension.Singleton.ofRegion Seed (t.typed inputSlots).packExits := by
  have eq : E [Bit] t.guarded (t.region inputSlots) Exits := expand_bit (i := 0) rfl (t.typed inputSlots).hasType
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).mpr
    (eq.lsubstPost t.guarded_typed (t.typed inputSlots) (fun _ _ hi =>
      (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hi).hasType))

theorem packed_replay (t : Tree 1) : t.packed = t.key.packed := by
  have same := region_replay t inputSlots
  have packed := (Paper.Extension.Singleton.ofRegion_eq_iff Seed
    (t.typed inputSlots).packExits (t.key.typed inputSlots).packExits).mpr
    (same.lsubstPost (t.typed inputSlots) (t.key.typed inputSlots) (fun _ _ hi =>
      (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hi).hasType))
  exact (packed_unguarded t).trans (packed.trans (packed_unguarded t.key).symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryQuotation
