module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Defs

/-! # Exact typing, renaming and outward shape -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns.BitFragment.Recursive
open Paper.WithCaseBind.BitQuery (signature Exits)
open Paper.WithCaseBind.BitQuery.RequestTree (Tree)
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (Live slots Direct)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit Answer)
open Silmaril.Isotope.LambdaSSA.Acyclic.Native (Outward)
open Silmaril.DeBruijn (lift)

local notation "U" => (Ty.unit : Ty Empty)

theorem request_typed {m : Nat} (label : Bool) (q : Query m) :
    Tm.HasType (Live m) (request label q) Answer := by
  apply Tm.HasType.op
  cases q with
  | read i => exact .var ((slots m).typed i)
  | known tag i dead =>
    have value : Tm.HasType (Live m) (.var i.val : Tm signature.Instr) Bit :=
      .var ((slots m).typed i)
    have bound : Tm.HasType (Bit :: Live m) (.var 0 : Tm signature.Instr) Bit :=
      .var (i := 0) rfl
    have older : Tm.HasType (Bit :: Live m) (.var (dead.val + 1) : Tm signature.Instr) Bit :=
      .var ((slots m).typed dead)
    cases tag
    · exact .case (.inl value) bound older
    · exact .case (.inr value) older bound

theorem term_typed {k n m : Nat} (c : Code k n) (ρ : Fin n → Fin m) :
    Tm.HasType (Live m) (c.term ρ) Bit := by
  induction c generalizing m with
  | ret _ i => exact .var ((slots m).typed (ρ i))
  | letUnit _ ih => exact .let₁ .unit ((ih ρ).rename (Ren.wk (Live m) U))
  | letBit _ _ ia ib => exact .let₁ (ia ρ) (ib (push ρ))
  | ask label i _ _ il ir => exact .case (request_typed label (i.map ρ)) (il (push ρ)) (ir (push ρ))

theorem region_typed {k n m : Nat} (c : Code k n) (ρ : Fin n → Fin m) :
    ValueBranches (Live m) (c.region ρ) (Live k) := by
  induction c generalizing m with
  | ret out i => exact .br ((slots _).typed out) (.var ((slots m).typed (ρ i)))
  | letUnit _ ih => exact .let₁ .unit ((ih ρ).renameVars (Ren.wk (Live m) U))
  | letBit a _ _ ih => exact .let₁ (term_typed a ρ) (ih (push ρ))
  | ask label i _ _ il ir => exact .case (request_typed label (i.map ρ)) (il (push ρ)) (ir (push ρ))

theorem normal_typed {k n : Nat} (t : Normal k n) :
    ValueBranches (Live n) t.region (Live k) := by
  induction t with
  | ret out i => exact .br ((slots _).typed out) (.var ((slots _).typed i))
  | ask label i _ _ il ir => exact .case (request_typed label (.read i)) il ir

private theorem push_rename {n m p : Nat} {ρ : Fin n → Fin m} {σ : Fin n → Fin p}
    {f : Nat → Nat} (h : ∀ i, f (ρ i).val = (σ i).val) (i : Fin (n + 1)) :
    lift f (push ρ i).val = (push σ i).val :=
  Fin.cases rfl (fun j => congrArg Nat.succ (h j)) i

private theorem request_rename {n m p : Nat} (label : Bool) (q : Query n)
    {ρ : Fin n → Fin m} {σ : Fin n → Fin p} {f : Nat → Nat}
    (h : ∀ i, f (ρ i).val = (σ i).val) :
    (request label (q.map ρ)).rename f = request label (q.map σ) := by
  cases q with
  | read i => simp only [request, Query.map, Query.term, Tm.rename, h i]
  | known tag i dead =>
    cases tag <;> simp only [request, Query.map, Query.term, Tm.rename, lift, h i, h dead]

private theorem term_rename {k n m p : Nat} (c : Code k n) (ρ : Fin n → Fin m)
    (σ : Fin n → Fin p) (f : Nat → Nat) (h : ∀ i, f (ρ i).val = (σ i).val) :
    (c.term ρ).rename f = c.term σ := by
  induction c generalizing m p f with
  | ret _ i => simp only [Code.term, Tm.rename, h i]
  | letUnit b ih =>
    simp only [Code.term, Tm.rename, Tm.rename_comp]
    change Tm.let₁ .unit ((b.term ρ).rename (Nat.succ ∘ f)) = _
    rw [← Tm.rename_comp, ih ρ σ f h]
  | letBit _ _ ia ib =>
    simp only [Code.term, Tm.rename, ia ρ σ f h, ib (push ρ) (push σ) (lift f) (push_rename h)]
  | ask label i _ _ il ir =>
    simp only [Code.term, Tm.rename, request_rename label i h, il (push ρ) (push σ) (lift f) (push_rename h),
      ir (push ρ) (push σ) (lift f) (push_rename h)]

theorem region_rename {k n m p : Nat} (c : Code k n) (ρ : Fin n → Fin m)
    (σ : Fin n → Fin p) (f : Nat → Nat) (h : ∀ i, f (ρ i).val = (σ i).val) :
    (c.region ρ).renameVars f = c.region σ := by
  induction c generalizing m p f with
  | ret _ i => simp only [Code.region, Region.renameVars, Tm.rename, h i]
  | letUnit b ih =>
    simp only [Code.region, Region.renameVars, Tm.rename, Region.renameVars_comp]
    change Region.let₁ .unit ((b.region ρ).renameVars (Nat.succ ∘ f)) = _
    rw [← Region.renameVars_comp, ih ρ σ f h]
  | letBit a _ _ ib =>
    simp only [Code.region, Region.renameVars, term_rename a ρ σ f h,
      ib (push ρ) (push σ) (lift f) (push_rename h)]
  | ask label i _ _ il ir =>
    simp only [Code.region, Region.renameVars, request_rename label i h,
      il (push ρ) (push σ) (lift f) (push_rename h), ir (push ρ) (push σ) (lift f) (push_rename h)]

private theorem lift_exit {σ : Nat → Region signature.Instr}
    (h : ∀ i, ∃ a, σ i = .br 0 a) : ∀ i, ∃ a, liftLSubstVars σ i = .br 0 a := by
  intro i
  obtain ⟨a, ha⟩ := h i
  exact ⟨a.rename (lift Nat.succ), by simp only [liftLSubstVars, ha, Region.renameVars]⟩

private theorem outward_post {k n m : Nat} (c : Code k n) (ρ : Fin n → Fin m)
    (f : Nat → Nat) (σ : Nat → Region signature.Instr) (h : ∀ i, ∃ a, σ i = .br 0 a) :
    Outward 0 (((c.region ρ).renameVars f).lsubst σ) := by
  induction c generalizing m f σ with
  | ret out i =>
    obtain ⟨a, ha⟩ := h out.val
    change Outward 0 ((σ out.val).substVars _)
    rw [ha]
    exact .br _
  | letUnit b ih =>
    apply Outward.let₁
    simpa only [Region.renameVars_comp] using ih ρ (lift f ∘ Nat.succ) (liftLSubstVars σ) (lift_exit h)
  | letBit _ _ _ ih =>
    exact .let₁ _ (ih (push ρ) (lift f) (liftLSubstVars σ) (lift_exit h))
  | ask _ _ _ _ il ir =>
    exact .case _ (il (push ρ) (lift f) (liftLSubstVars σ) (lift_exit h))
      (ir (push ρ) (lift f) (liftLSubstVars σ) (lift_exit h))

theorem outward_packed {k n m : Nat} (c : Code k n) (ρ : Fin n → Fin m) :
    Outward 0 (c.region ρ).packExits := by
  unfold Region.packExits
  simpa only [Region.renameVars_id] using
    outward_post c ρ id (fun i => .br 0 (packedExitArg i (.var 0))) (fun i => ⟨_, rfl⟩)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive
