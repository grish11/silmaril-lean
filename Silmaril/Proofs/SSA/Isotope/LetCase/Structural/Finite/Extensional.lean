module

public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Substitution

public section

namespace Silmaril.Isotope.LetCase.Structural.Finite

open LocallyNameless (Equiv HasType Tm TypedSubst)
open Reply (Γ₀ specialize)
open scoped Silmaril.Isotope.LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [Signature Φ]
set_option backward.isDefEq.respectTransparency false

omit [Signature Φ] in
private theorem instantiate_weakened {n : Nat} (k v : Term Φ (n + 1)) :
    Tm.instantiate k.underBinder v = specialize k v := by
  rw [Tm.instantiate, Tm.underBinder, Tm.bsubst_rename]
  exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k

omit [Signature Φ] in
private theorem specialize_identity {n : Nat} (k : Term Φ (n + 1)) :
    specialize k (.bv 0) = k :=
  (Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k).trans (Tm.bsubst_id k)

private theorem unit_replay {n : Nat} {β : Context n} {k : Term Φ (n + 1)} {D : Types}
    (dk : HasType Φ Γ₀ (β.snoc .unit) k D) :
    Equiv false Γ₀ (β.snoc .unit) k (Tm.instantiate k .unit).lift D := by
  have slot : HasType Φ Γ₀ (β.snoc .unit) (.bv 0) .unit := .bv
  have start := Equiv.letBeta (pureEff := false) .bv slot dk.underBinder
  rw [instantiate_weakened, specialize_identity] at start
  have unit := (Equiv.unitEta (pureEff := false) slot).symm.trans
    (Equiv.letBeta .bv slot (HasType.unit (β := (β.snoc .unit).snoc .unit)))
  have finish := Equiv.letBeta (pureEff := false) .unit
    (HasType.unit (β := β.snoc .unit)) dk.underBinder
  rw [instantiate_weakened] at finish
  have openUnit : specialize k .unit = (Tm.instantiate k .unit).lift := by
    rw [specialize, Tm.lift, Tm.instantiate, Tm.rename_bsubst]
    exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k
  rw [openUnit] at finish
  exact start.symm.trans ((Equiv.let₁ unit (.refl dk.underBinder)).trans finish)

private def pairBody {n : Nat} (k : Term Φ (n + 1)) : Term Φ (n + 2) :=
  k.bsubst (Fin.cases (.pair (.bv 1) (.bv 0)) (fun i => .bv i.succ.succ))

private theorem pairBody_typed {n : Nat} {β : Context n} {k : Term Φ (n + 1)}
    {A B D : Types} (dk : HasType Φ Γ₀ (β.snoc (.product A B)) k D) :
    HasType Φ Γ₀ ((β.snoc A).snoc B) (pairBody k) D := by
  apply dk.bsubst
  exact Fin.cases (HasType.pair .bv .bv) (fun _ => .bv)

private theorem pair_replay {n : Nat} {β : Context n} {k : Term Φ (n + 1)} {A B D : Types}
    (dk : HasType Φ Γ₀ (β.snoc (.product A B)) k D) :
    Equiv false Γ₀ (β.snoc (.product A B)) k (.let₂ (.bv 0) (pairBody k).underTwoBinders) D := by
  have slot : HasType Φ Γ₀ (β.snoc (.product A B)) (.bv 0) (.product A B) := .bv
  have parts : HasType Φ Γ₀ (((β.snoc (.product A B)).snoc A).snoc B)
      (.pair (.bv 1) (.bv 0)) (.product A B) := .pair .bv .bv
  have start := Equiv.letBeta (pureEff := false) .bv slot dk.underBinder
  rw [instantiate_weakened, specialize_identity] at start
  have finish := Equiv.letBeta (pureEff := false) (.pair .bv .bv) parts
    dk.underBinder.underBinder.underBinder
  have unpack : Tm.instantiate k.underBinder.underBinder.underBinder (.pair (.bv 1) (.bv 0)) =
      (pairBody k).underTwoBinders := by
    simp only [Tm.instantiate, Tm.underBinder, Tm.underTwoBinders, pairBody,
      Tm.bsubst_rename, Tm.rename_bsubst]
    exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k
  rw [unpack] at finish
  exact start.symm.trans ((Equiv.let₁ (Equiv.pairEta slot).symm (.refl dk.underBinder)).trans
    ((Equiv.bindLetPair slot parts dk.underBinder).trans (.let₂ (.refl slot) finish)))

omit [Signature Φ] in
private theorem instantiate_inl {n : Nat} {A : Types} (k : Term Φ (n + 1)) (a : Constructor A) :
    Tm.instantiate (specialize k (.inl (.bv 0))) a.term = Tm.instantiate k (.inl a.term) := by
  rw [specialize, Tm.instantiate, Tm.bsubst_comp]
  exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k

omit [Signature Φ] in
private theorem instantiate_inr {n : Nat} {B : Types} (k : Term Φ (n + 1)) (b : Constructor B) :
    Tm.instantiate (specialize k (.inr (.bv 0))) b.term = Tm.instantiate k (.inr b.term) := by
  rw [specialize, Tm.instantiate, Tm.bsubst_comp]
  exact Tm.bsubst_congr (Fin.cases rfl (fun _ => rfl)) k

omit [Signature Φ] in
private theorem instantiate_pair {n : Nat} {A B : Types} (k : Term Φ (n + 1))
    (a : Constructor A) (b : Constructor B) :
    Tm.instantiate (Tm.instantiate (pairBody k) b.term) a.term = Tm.instantiate k (.pair a.term b.term) := by
  simp only [pairBody, Tm.instantiate, Tm.bsubst_comp]
  apply Tm.bsubst_congr
  refine Fin.cases ?_ (fun _ => rfl)
  change (.pair a.term (Tm.bsubst (Fin.cases a.term (fun i => .bv i)) b.term) : Term Φ n) =
    .pair a.term b.term
  rw [Constructor.term_bsubst]

/-- All typed bodies in an empty slot agree by native empty initiality. -/
theorem empty_slot_proof {n : Nat} {β : Context n} {D : Types} {t u : Term Φ (n + 1)}
    (dt : HasType Φ Γ₀ (β.snoc .empty) t D) (du : HasType Φ Γ₀ (β.snoc .empty) u D) :
    Equiv false Γ₀ (β.snoc .empty) t u D := by
  have slot : HasType Φ Γ₀ (β.snoc .empty) (.bv 0) .empty := .bv
  have abort : HasType Φ Γ₀ (β.snoc .empty) (.abort (.bv 0)) .unit := .abort slot
  have left := Equiv.letBeta (pureEff := false) (.abort .bv) abort dt.lift
  have right := Equiv.letBeta (pureEff := false) (.abort .bv) abort du.lift
  rw [open_lift] at left right
  exact left.symm.trans ((Equiv.emptyInitial (A := Ty.unit) slot dt.lift du.lift).trans right)

/-- Native extensionality at one atom-free slot, including empty summands.
The ambient context is arbitrary and the bodies may have effects. -/
theorem constructor_ext_type_proof (X : Types) {n : Nat} {β : Context n} {D : Types}
    {t u : Term Φ (n + 1)}
    (dt : HasType Φ Γ₀ (β.snoc X) t D) (du : HasType Φ Γ₀ (β.snoc X) u D)
    (h : ∀ v : Constructor X,
      Equiv false Γ₀ β (Tm.instantiate t v.term) (Tm.instantiate u v.term) D) :
    Equiv false Γ₀ (β.snoc X) t u D := by
  induction X generalizing n with
  | base a => exact a.elim
  | empty => exact empty_slot_proof dt du
  | unit => exact (unit_replay dt).trans (((h .unit).lift (X := .unit)).trans (unit_replay du).symm)
  | coprod A B iha ihb =>
    apply (Reply.equiv_iff_specializations dt du).mpr
    refine ⟨?_, ?_⟩
    · apply iha (dt.bsubst (Fin.cases (.inl .bv) (fun _ => .bv)))
        (du.bsubst (Fin.cases (.inl .bv) (fun _ => .bv)))
      intro a
      change Equiv false Γ₀ β (Tm.instantiate (specialize t (.inl (.bv 0))) a.term)
        (Tm.instantiate (specialize u (.inl (.bv 0))) a.term) D
      rw [instantiate_inl, instantiate_inl]
      exact h (.inl a)
    · apply ihb (dt.bsubst (Fin.cases (.inr .bv) (fun _ => .bv)))
        (du.bsubst (Fin.cases (.inr .bv) (fun _ => .bv)))
      intro b
      change Equiv false Γ₀ β (Tm.instantiate (specialize t (.inr (.bv 0))) b.term)
        (Tm.instantiate (specialize u (.inr (.bv 0))) b.term) D
      rw [instantiate_inr, instantiate_inr]
      exact h (.inr b)
  | product A B iha ihb =>
    have pt := pairBody_typed dt
    have pu := pairBody_typed du
    have parts : Equiv false Γ₀ ((β.snoc A).snoc B) (pairBody t) (pairBody u) D := by
      apply ihb pt pu
      intro b
      apply iha (pt.instantiate b.typing.toHasType) (pu.instantiate b.typing.toHasType)
      intro a
      rw [instantiate_pair, instantiate_pair]
      exact h (.pair a b)
    exact (pair_replay dt).trans ((Equiv.let₂ (.refl .bv) parts.underTwoBinders).trans (pair_replay du).symm)

end Silmaril.Isotope.LetCase.Structural.Finite
