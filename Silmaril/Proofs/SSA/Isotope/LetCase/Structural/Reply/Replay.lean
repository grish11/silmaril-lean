module

public import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Defs

public section

namespace Silmaril.Isotope.LetCase.Structural.Reply

open LocallyNameless (Equiv HasType Pure PureTypedSubst Tm)
open scoped LetSeq.StraightLine.Structural

variable {α Φ : Type} [HasTy Φ (Ty α)]
set_option backward.isDefEq.respectTransparency false

omit [HasTy Φ (Ty α)] in
private theorem specialize_instantiate {n : Nat} (k v : Tm Empty Φ (n + 1)) :
    Tm.instantiate k.underBinder v = specialize k v := by
  rw [Tm.instantiate, Tm.underBinder, Tm.bsubst_rename]
  exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k

/-- Split a let-bound sum into its native constructor specializations. The
scrutinee can be any exact term and is still evaluated once. -/
theorem split_let_proof {n : Nat} {β : BoundCtx (Ty α) n} {e : Tm Empty Φ n}
    {k : Tm Empty Φ (n + 1)} {A B D : Ty α}
    (de : HasType Φ Γ₀ β e (.coprod A B))
    (dk : HasType Φ Γ₀ (β.snoc (.coprod A B)) k D) :
    Equiv false Γ₀ β (.let₁ e k)
      (.case e (specialize k (.inl (.bv 0))) (specialize k (.inr (.bv 0)))) D := by
  have left : HasType Φ Γ₀ (β.snoc A) (.inl (.bv 0)) (.coprod A B) := .inl .bv
  have right : HasType Φ Γ₀ (β.snoc B) (.inr (.bv 0)) (.coprod A B) := .inr .bv
  have armL := Equiv.letBeta (pureEff := false) (.inl .bv) left dk.underBinder
  have armR := Equiv.letBeta (pureEff := false) (.inr .bv) right dk.underBinder
  rw [specialize_instantiate] at armL armR
  exact (Equiv.let₁ (Equiv.caseEta de).symm (.refl dk)).trans
    ((Equiv.bindLetCase de left right dk).trans (.case (.refl de) armL armR))

omit [HasTy Φ (Ty α)] in
private theorem specialize_underBinder {n : Nat} (k v : Tm Empty Φ (n + 1)) :
    (specialize k v).underBinder = specialize k.underBinder v.underBinder := by
  unfold specialize Tm.underBinder
  rw [Tm.rename_bsubst, Tm.bsubst_rename]
  exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k

private theorem split_slot {n : Nat} {β : BoundCtx (Ty α) n}
    {k : Tm Empty Φ (n + 1)} {A B D : Ty α}
    (dk : HasType Φ Γ₀ (β.snoc (.coprod A B)) k D) :
    Equiv false Γ₀ (β.snoc (.coprod A B)) k
      (.case (.bv 0) (specialize k (.inl (.bv 0))).underBinder
        (specialize k (.inr (.bv 0))).underBinder) D := by
  have slot : HasType Φ Γ₀ (β.snoc (.coprod A B)) (.bv 0) (.coprod A B) := .bv
  have openSlot := Equiv.letBeta (pureEff := false) .bv slot dk.underBinder
  rw [specialize_instantiate] at openSlot
  have identity : specialize k (.bv 0) = k :=
    (Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k).trans (Tm.bsubst_id k)
  rw [identity] at openSlot
  have split := split_let_proof slot dk.underBinder
  rw [specialize_underBinder, specialize_underBinder]
  exact openSlot.symm.trans split

/-- Native contextual sum extensionality, with no purity restriction on
either body. Only the newly substituted injection is pure. -/
private theorem equiv_of_specializations {n : Nat} {β : BoundCtx (Ty α) n}
    {t u : Tm Empty Φ (n + 1)} {A B D : Ty α}
    (dt : HasType Φ Γ₀ (β.snoc (.coprod A B)) t D)
    (du : HasType Φ Γ₀ (β.snoc (.coprod A B)) u D)
    (left : Equiv false Γ₀ (β.snoc A) (specialize t (.inl (.bv 0))) (specialize u (.inl (.bv 0))) D)
    (right : Equiv false Γ₀ (β.snoc B) (specialize t (.inr (.bv 0))) (specialize u (.inr (.bv 0))) D) :
    Equiv false Γ₀ (β.snoc (.coprod A B)) t u D :=
  (split_slot dt).trans ((Equiv.case (.refl .bv) left.underBinder right.underBinder).trans (split_slot du).symm)

theorem equiv_iff_specializations_proof {n : Nat} {β : BoundCtx (Ty α) n}
    {t u : Tm Empty Φ (n + 1)} {A B D : Ty α}
    (dt : HasType Φ Γ₀ (β.snoc (.coprod A B)) t D)
    (du : HasType Φ Γ₀ (β.snoc (.coprod A B)) u D) :
    Equiv false Γ₀ (β.snoc (.coprod A B)) t u D ↔
      Equiv false Γ₀ (β.snoc A) (specialize t (.inl (.bv 0))) (specialize u (.inl (.bv 0))) D ∧
      Equiv false Γ₀ (β.snoc B) (specialize t (.inr (.bv 0))) (specialize u (.inr (.bv 0))) D := by
  refine ⟨fun eq => ?_, fun arms => equiv_of_specializations dt du arms.1 arms.2⟩
  have left : PureTypedSubst false Γ₀ (β.snoc (.coprod A B)) (β.snoc A)
      (Fin.cases (.inl (.bv 0)) (fun i => .bv i.succ)) :=
    ⟨Fin.cases (.inl .bv) (fun _ => .bv), fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · change Pure false (.inl (.bv (0 : Fin (n + 1))) : Tm Empty Φ (n + 1))
        exact .inl .bv
      · change Pure false (.bv j.succ : Tm Empty Φ (n + 1))
        exact .bv⟩
  have right : PureTypedSubst false Γ₀ (β.snoc (.coprod A B)) (β.snoc B)
      (Fin.cases (.inr (.bv 0)) (fun i => .bv i.succ)) :=
    ⟨Fin.cases (.inr .bv) (fun _ => .bv), fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · change Pure false (.inr (.bv (0 : Fin (n + 1))) : Tm Empty Φ (n + 1))
        exact .inr .bv
      · change Pure false (.bv j.succ : Tm Empty Φ (n + 1))
        exact .bv⟩
  exact ⟨eq.bsubst left, eq.bsubst right⟩

end Silmaril.Isotope.LetCase.Structural.Reply
