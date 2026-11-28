module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest

open Isotope.LetCase.LocallyNameless (Equiv HasType Tm)

set_option backward.isDefEq.respectTransparency false

local notation "Γ₀" => (Ctx.nil : Ctx Empty Sorts)
local notation "U" => (Ty.unit : Sorts)
local notation "Term" => Tm Empty signature.Instr

private theorem instantiate_lift {k : Nat} (a t : Term k) :
    Tm.instantiate t.lift a = t := by
  unfold Tm.instantiate Tm.lift
  rw [Tm.bsubst_rename]
  exact Tm.bsubst_id t

/-- Remove the abstract test binder. This preserves the request binder and
the unit binder of each newly selected arm. -/
private theorem subst_arm {k : Nat} (original : Term (k + 1)) (init : Term k) :
    Tm.bsubst (Tm.upSub (Tm.upSub (Fin.cases init (fun i => .bv i))))
      original.underBinder.lift = original.lift := by
  simp only [Tm.bsubst_lift]
  unfold Tm.underBinder
  rw [Tm.bsubst_rename]
  congr 1
  apply (Tm.bsubst_congr _ original).trans (Tm.bsubst_id original)
  intro i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem subst_open {k : Nat} (q : Term k) (l r : Term (k + 1)) (d : Term k) :
    Tm.instantiate (.let₁ q.lift (.case (.bv 1) l.underBinder.lift r.underBinder.lift)) d =
      .let₁ q (.case d.lift l.lift r.lift) := by
  unfold Tm.instantiate
  rw [Tm.bsubst_let₁]
  rw [show Tm.bsubst (Fin.cases d (fun i => .bv i)) q.lift = q from instantiate_lift d q]
  simp only [Tm.bsubst_case, subst_arm]
  rfl

private theorem subst_selected {k : Nat} (q : Term k) (l r : Term (k + 1)) (a : Term (k + 1)) :
    Tm.instantiate (Tm.underBinder (.let₁ q.lift (.case (.bv 1) l.underBinder.lift r.underBinder.lift))) a =
      .let₁ q.lift (.case a.lift l.underBinder.lift r.underBinder.lift) := by
  let shift : Fin (k + 1) → Fin (k + 2) := Tm.up Fin.succ
  change Tm.instantiate (Tm.rename shift (.let₁ q.lift (.case (.bv 1) l.underBinder.lift r.underBinder.lift))) a = _
  have q₀ : Tm.rename shift q.lift = q.lift.lift := Tm.rename_lift Fin.succ q
  have arms (s : Term (k + 1)) :
      Tm.rename (Tm.up shift) s.underBinder = s.underBinder.underBinder := by
    change Tm.rename (Tm.up (Tm.up Fin.succ)) s.underBinder =
      (Tm.rename (Tm.up Fin.succ) s).underBinder
    exact Tm.rename_underBinder Fin.succ s
  have slot : Tm.up shift (1 : Fin (k + 2)) = (1 : Fin (k + 3)) := rfl
  simp only [Tm.rename_let₁, Tm.rename_case, Tm.rename_bv, q₀, slot, Tm.rename_lift, arms]
  exact subst_open q.lift l.underBinder r.underBinder a

theorem factor_proof {k : Nat} {β : BoundCtx Sorts k} {i : Fin k} {A B : Sorts}
    {q : Term k} {l r : Term (k + 1)}
    (hd : HasType signature.Instr Γ₀ β (.bv i) Bit)
    (hq : HasType signature.Instr Γ₀ β q A)
    (hl : HasType signature.Instr Γ₀ (β.snoc A) l B)
    (hr : HasType signature.Instr Γ₀ (β.snoc A) r B) :
    Equiv false Γ₀ β (.case (.bv i) (.let₁ q.lift l.underBinder) (.let₁ q.lift r.underBinder))
      (.let₁ q (.case (.bv i.succ) l.lift r.lift)) B := by
  let c : Term (k + 1) := .let₁ q.lift (.case (.bv 1) l.underBinder.lift r.underBinder.lift)
  have hc : HasType signature.Instr Γ₀ (β.snoc Bit) c B :=
    .let₁ hq.lift (.case .bv hl.underBinder.lift hr.underBinder.lift)
  have abstract := Equiv.letBeta (pureEff := false) .bv hd hc
  change Equiv false Γ₀ β (.let₁ (.bv i) c)
    (Tm.instantiate (.let₁ q.lift (.case (.bv 1) l.underBinder.lift r.underBinder.lift)) (.bv i)) B at abstract
  rw [subst_open] at abstract
  have low : HasType signature.Instr Γ₀ (β.snoc U) (.inl (.bv 0)) Bit := .inl .bv
  have high : HasType signature.Instr Γ₀ (β.snoc U) (.inr (.bv 0)) Bit := .inr .bv
  have eta := Equiv.let₁ (Equiv.caseEta (pureEff := false) hd).symm (.refl hc)
  have distribute := Equiv.bindLetCase (pureEff := false) hd low high hc
  have selectLow := Equiv.letBeta (pureEff := false) (.inl .bv) low hc.underBinder
  have selectHigh := Equiv.letBeta (pureEff := false) (.inr .bv) high hc.underBinder
  unfold c at selectLow selectHigh
  rw [subst_selected] at selectLow selectHigh
  have unitSlot : HasType signature.Instr Γ₀ ((β.snoc U).snoc A) (.bv 1) U := .bv
  have left : HasType signature.Instr Γ₀ (((β.snoc U).snoc A).snoc U) l.underBinder.lift B :=
    hl.underBinder.lift
  have right : HasType signature.Instr Γ₀ (((β.snoc U).snoc A).snoc U) r.underBinder.lift B :=
    hr.underBinder.lift
  have reduceL := Equiv.letBeta (pureEff := false) .bv unitSlot left
  have reduceR := Equiv.letBeta (pureEff := false) .bv unitSlot right
  rw [instantiate_lift] at reduceL reduceR
  have lowRight := selectLow.trans (.let₁ (.refl hq.lift)
    ((Equiv.caseBetaL unitSlot left right).trans reduceL))
  have highRight := selectHigh.trans (.let₁ (.refl hq.lift)
    ((Equiv.caseBetaR unitSlot left right).trans reduceR))
  exact (eta.trans (distribute.trans (.case (.refl hd) lowRight highRight))).symm.trans abstract

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest
