module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Branch.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch

open Sequence (Body Sorts Normal signature)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Acyclic.Positional.Capture (Scope)
open Isotope.LetCase.LocallyNameless (AbortCongr AbortEquiv Equiv HasType Tm)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)

private theorem operand_rename (a : Arm) {n m : Nat} {β : BoundCtx Sorts n} {δ : BoundCtx Sorts m}
    (ρ : BoundCtx.Renaming β δ) :
    (⟨_, (a.operand β).2.rename ρ⟩ : Operand signature.Instr δ U) = a.operand δ := by
  cases a with
  | body p => exact p.operand_rename ρ
  | known tag l r =>
    have left := l.operand_rename (ρ.up U)
    have right := r.operand_rename (ρ.up U)
    cases tag
    · exact congrArg₂ (fun (l r : Operand signature.Instr (δ.snoc U) U) =>
        (⟨.case (.inl .unit) l.1 r.1, .case (.inl .unit) l.2 r.2⟩ : Operand signature.Instr δ U))
        left right
    · exact congrArg₂ (fun (l r : Operand signature.Instr (δ.snoc U) U) =>
        (⟨.case (.inr .unit) l.1 r.1, .case (.inr .unit) l.2 r.2⟩ : Operand signature.Instr δ U))
        left right

theorem program_rendered_proof (tail : List Sorts) (p : ProgramBody) :
    (p.program tail).toLetCase = p.rendered tail := by
  let s : Scope inputContext (inputContext.snoc Input) := .skip .base Input
  have arm (a : Arm) : s.operand (a.operand (inputContext.snoc U)) = a.operand branchContext :=
    operand_rename a (s.renaming.up U)
  change (LambdaSSA.Acyclic.FiniteExit.join (.br ⟨.bv 0, .bv⟩)
    (.case ⟨.bv 0, .bv⟩
      (.join (.br (s.operand (p.left.operand _))) (.br (i := 0) rfl ⟨.bv 0, .bv⟩))
      (.join (.br (s.operand (p.right.operand _))) (.br (i := 0) rfl ⟨.bv 0, .bv⟩)))).encode.toLetCase = _
  rw [arm p.left, arm p.right]
  rfl

private theorem select_arm (a : Arm) {n : Nat} (β : BoundCtx Sorts n) :
    Equiv false Γ₀ β (a.operand β).1 (a.selected.operand β).1 U := by
  cases a with
  | body p => exact .refl (p.operand β).2.toHasType
  | known tag l r =>
    have lit : HasType signature.Instr Γ₀ β .unit U := .unit
    have left := (l.operand (β.snoc U)).2.toHasType
    have right := (r.operand (β.snoc U)).2.toHasType
    have beta (p : Body) : Equiv false Γ₀ β (.let₁ .unit (p.operand (β.snoc U)).1)
        (p.operand β).1 U := by
      have h := Equiv.letBeta (pureEff := false) .unit lit (p.operand (β.snoc U)).2.toHasType
      simpa only [Tm.instantiate, p.operand_bsubst (β.snoc U) β] using h
    cases tag
    · exact (Equiv.caseBetaL lit left right).trans (beta l)
    · exact (Equiv.caseBetaR lit left right).trans (beta r)

theorem normalize_arm_proof (a : Arm) {n : Nat} (β : BoundCtx Sorts n) :
    AbortEquiv false Γ₀ β (a.operand β).1 (a.selected.canonical.operand β).1 U :=
  .trans (.equiv (select_arm a β)) (AbortCongr.toAbortEquiv (a.selected.normalize β))

private theorem arms_equiv (a b : Arm) {n : Nat} (β : BoundCtx Sorts n)
    (h : a.selected.normal = b.selected.normal) :
    AbortEquiv false Γ₀ β (a.operand β).1 (b.operand β).1 U := by
  have canonical := congrArg (fun nf : Normal => Normal.body nf.1 nf.2) h
  have left := normalize_arm_proof a β
  change a.selected.canonical = b.selected.canonical at canonical
  rw [canonical] at left
  exact left.trans (normalize_arm_proof b β).symm

theorem repaired_of_normal_proof (tail : List Sorts) (p q : ProgramBody) (h : p.normal = q.normal) :
    Repaired false (equation tail p q) := by
  change AbortEquiv false Γ₀ inputContext (p.program tail).toLetCase.1 (q.program tail).toLetCase.1 _
  rw [program_rendered_proof, program_rendered_proof]
  exact .let₁ (.equiv (.refl .bv)) (.case (.equiv (.refl .bv))
    (.let₁ (arms_equiv p.left q.left branchContext (congrArg Prod.fst h)) (.equiv (.refl (.inl .bv))))
    (.let₁ (arms_equiv p.right q.right branchContext (congrArg Prod.snd h)) (.equiv (.refl (.inl .bv)))))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch
