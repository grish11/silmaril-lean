module

public import Silmaril.Logic.CommonLogic.ManySorted.Expansion.Defs

/-! Structure isomorphism and satisfaction transport for tagged expansions.
The local transport argument follows GuardedFOL without importing its proof modules. -/
@[expose] public section
noncomputable section

namespace Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic Silmaril.Logic.CommonLogic.ManySorted
open Silmaril.Logic.CommonLogic.ManySorted.Expansion

variable {S : FOL.Signature}

theorem unpack_op (M : FOL.Structure S) {n : Nat} {w : Fin n → S.S} {s : S.S}
    (o : S.Op n w s) (args : ∀ i, (decode (expand M)).carrier (w i)) :
    unpack M ((decode (expand M)).op o args) = M.op o (fun i => unpack M (args i)) := by
  have hargs : (fun i => (args i).val) = fun i => tag M (w i) (unpack M (args i)) :=
    funext (fun i => unpack_spec M (args i))
  have hval : ((decode (expand M)).op o args).val =
      tag M s (M.op o (fun i => unpack M (args i))) := by
    change (raw M).function ((raw M).nondiscourse (.op o))
      (List.ofFn (fun i => (args i).val)) = _
    rw [hargs]
    exact function_encode M o _
  exact tag_injective M s ((unpack_spec M _).symm.trans hval)

theorem unpack_rel (M : FOL.Structure S) {n : Nat} {w : Fin n → S.S}
    (r : S.Rel n w) (args : ∀ i, (decode (expand M)).carrier (w i)) :
    (decode (expand M)).rel r args ↔ M.rel r (fun i => unpack M (args i)) := by
  have hargs : (fun i => (args i).val) = fun i => tag M (w i) (unpack M (args i)) :=
    funext (fun i => unpack_spec M (args i))
  change (raw M).relation ((raw M).nondiscourse (.rel r))
    (List.ofFn (fun i => (args i).val)) ↔ _
  rw [hargs]
  exact relation_encode M r _

private theorem structureHom_ext {M N : FOL.Structure S} (f g : M ⟶ N)
    (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

/-- Recovery in the actual public category of FOL structures, not carrier equality. -/
def decodeExpandIso (M : FOL.Structure S) : decode (expand M) ≅ M where
  hom := ⟨fun _ => unpack M, unpack_op M, fun r args h => (unpack_rel M r args).mp h⟩
  inv := {
    map := pack M
    map_op := by
      intro n w s o args
      apply (carrierEquiv M s).injective
      change unpack M (pack M s (M.op o args)) =
        unpack M ((decode (expand M)).op o (fun i => pack M (w i) (args i)))
      rw [unpack_pack, unpack_op]
      exact congrArg (M.op o) (funext (fun i => (unpack_pack M (w i) (args i)).symm))
    map_rel := by
      intro n w r args hr
      apply (unpack_rel M r _).mpr
      simpa only [unpack_pack] using hr }
  hom_inv_id := by
    apply structureHom_ext
    funext s x
    exact pack_unpack M x
  inv_hom_id := by
    apply structureHom_ext
    funext s x
    exact unpack_pack M s x

/- The following generic proof pattern is copied/adapted from the private source
Silmaril/Proofs/Logic/Matching/GuardedFOL/{Contexts,Expansion}.lean at base755a.
It is local to this proof module to avoid importing another topic's Proofs. -/
private theorem context_eq {S : Type} {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) : Δ = Fin.cases (Δ 0) Γ := by
  funext i
  exact Fin.cases rfl (congrFun h) i

private def extend {S : Type} (C : S → Type) {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) (v : ∀ i, C (Γ i)) (x : C (Δ 0)) : ∀ i, C (Δ i) :=
  Eq.rec (motive := fun Θ _ => ∀ i, C (Θ i)) (Fin.cases x v) (context_eq h).symm

private theorem context_cast_apply {S : Type} (C : S → Type) {k : Nat} {Γ Δ : Fin k → S}
    (h : Γ = Δ) (v : ∀ i, C (Γ i)) (i : Fin k) :
    HEq ((h ▸ v : ∀ i, C (Δ i)) i) (v i) := by cases h; rfl

private theorem extend_zero {S : Type} (C : S → Type) {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) (v : ∀ i, C (Γ i)) (x : C (Δ 0)) : extend C h v x 0 = x := by
  unfold extend
  exact eq_of_heq (context_cast_apply C (context_eq h).symm
    (show (∀ i, C (Fin.cases (Δ 0) Γ i)) from Fin.cases x v) 0)

private theorem extend_succ {S : Type} (C : S → Type) {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) (v : ∀ i, C (Γ i)) (x : C (Δ 0)) (i : Fin k) :
    HEq (extend C h v x i.succ) (v i) := by
  unfold extend
  exact context_cast_apply C (context_eq h).symm
    (show (∀ i, C (Fin.cases (Δ 0) Γ i)) from Fin.cases x v) i.succ

private theorem forall_extensions {S : Type} (C : S → Type) {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S}
    (h : Δ ∘ Fin.succ = Γ) (v : ∀ i, C (Γ i)) (P : (∀ i, C (Δ i)) → Prop) :
    (∀ x, P (extend C h v x)) ↔ ∀ θ, (∀ i, HEq (θ i.succ) (v i)) → P θ := by
  constructor
  · intro hall θ hθ
    have same : extend C h v (θ 0) = θ := by
      funext i
      cases i using Fin.cases with
      | zero => exact extend_zero C h v (θ 0)
      | succ i => exact eq_of_heq ((extend_succ C h v (θ 0) i).trans (hθ i).symm)
    exact same ▸ hall (θ 0)
  · intro hall x
    exact hall _ (extend_succ C h v x)

private theorem cast_natural {S : Type} {C D : S → Type} (f : ∀ s, C s → D s)
    {k : Nat} {Γ Δ : Fin k → S} (h : Γ = Δ) (v : ∀ i, C (Γ i)) :
    (fun i => f (Δ i) ((h ▸ v : ∀ i, C (Δ i)) i)) =
      (h ▸ (fun i => f (Γ i) (v i)) : ∀ i, D (Δ i)) := by cases h; rfl

private theorem extend_natural {S : Type} {C D : S → Type} (f : ∀ s, C s → D s)
    {k : Nat} {Γ : Fin k → S} {Δ : Fin (k+1) → S} (h : Δ ∘ Fin.succ = Γ)
    (v : ∀ i, C (Γ i)) (x : C (Δ 0)) :
    (fun i => f (Δ i) (extend C h v x i)) = extend D h (fun i => f (Γ i) (v i)) (f (Δ 0) x) := by
  unfold extend
  rw [cast_natural]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Evaluation commutes with actual FOL structure homomorphisms. -/
private theorem eval_hom {M N : FOL.Structure S} (f : M ⟶ N) {k : Nat} {Γ : Fin k → S.S}
    {s : S.S} (t : EQ.Term S.toSignature Γ s) (v : ∀ i, M.carrier (Γ i)) :
    f.map s (t.eval M.toAlgebra v) = t.eval N.toAlgebra (fun i => f.map (Γ i) (v i)) := by
  induction t with
  | var => rfl
  | app op args ih =>
      change f.map _ (M.op op _) = N.op op _
      rw [f.map_op]
      exact congrArg (N.op op) (funext ih)

private def isoCarrierEquiv {M N : FOL.Structure S} (e : M ≅ N) (s : S.S) : M.carrier s ≃ N.carrier s where
  toFun := e.hom.map s
  invFun := e.inv.map s
  left_inv x := congrArg (fun f : M ⟶ M => f.map s x) e.hom_inv_id
  right_inv x := congrArg (fun f : N ⟶ N => f.map s x) e.inv_hom_id

/-- Formula truth transport is proved through the actual structure isomorphism. -/
private theorem holds_iso {M N : FOL.Structure S} (e : M ≅ N) {k : Nat} {Γ : Fin k → S.S}
    (p : FOL.Formula S Γ) : ∀ v,
    p.Holds M v ↔ p.Holds N (fun i => e.hom.map (Γ i) (v i)) := by
  induction p with
  | eq t u =>
      intro v
      change t.eval M.toAlgebra v = u.eval M.toAlgebra v ↔
        t.eval N.toAlgebra (fun i => e.hom.map _ (v i)) = u.eval N.toAlgebra (fun i => e.hom.map _ (v i))
      rw [← eval_hom e.hom t v, ← eval_hom e.hom u v]
      exact (isoCarrierEquiv e _).injective.eq_iff.symm
  | @rel k Γ n inputs r args =>
      show ∀ v, (FOL.Formula.rel r args).Holds M v ↔
        (FOL.Formula.rel r args).Holds N (fun i => e.hom.map (Γ i) (v i))
      intro v
      change M.rel r (fun i => (args i).eval M.toAlgebra v) ↔
        N.rel r (fun i => (args i).eval N.toAlgebra (fun j => e.hom.map _ (v j)))
      have heval : (fun i => (args i).eval N.toAlgebra (fun j => e.hom.map _ (v j))) =
          (fun i => e.hom.map _ ((args i).eval M.toAlgebra v)) := funext fun i => (eval_hom e.hom (args i) v).symm
      rw [heval]
      constructor
      · exact e.hom.map_rel r _
      · intro hr
        have hback : M.rel r (fun i => e.inv.map _ (e.hom.map _ ((args i).eval M.toAlgebra v))) :=
          e.inv.map_rel r _ hr
        have hsame : (fun i => e.inv.map _ (e.hom.map _ ((args i).eval M.toAlgebra v))) =
            (fun i => (args i).eval M.toAlgebra v) := funext fun i => (isoCarrierEquiv e _).left_inv _
        exact hsame ▸ hback
  | tt => intro v; rfl
  | not p ih => intro v; exact not_congr (ih v)
  | and p q hp hq => intro v; exact and_congr (hp v) (hq v)
  | @all k Γ Δ h p ih =>
      show ∀ v, (FOL.Formula.all h p).Holds M v ↔
        (FOL.Formula.all h p).Holds N (fun i => e.hom.map (Γ i) (v i))
      intro v
      change (∀ θ, (∀ i, HEq (θ i.succ) (v i)) → p.Holds M θ) ↔
        ∀ θ, (∀ i, HEq (θ i.succ) (e.hom.map _ (v i))) → p.Holds N θ
      rw [← forall_extensions M.carrier h v, ← forall_extensions N.carrier h (fun i => e.hom.map _ (v i))]
      constructor
      · intro hall y
        obtain ⟨x, rfl⟩ := (isoCarrierEquiv e (Δ 0)).surjective y
        change p.Holds N (extend N.carrier h (fun i => e.hom.map _ (v i)) (e.hom.map _ x))
        rw [← extend_natural e.hom.map h v x]
        exact (ih _).mp (hall x)
      · intro hall x
        have hx : p.Holds N (extend N.carrier h (fun i => e.hom.map _ (v i)) (e.hom.map _ x)) :=
          hall (e.hom.map _ x)
        rw [← extend_natural e.hom.map h v x] at hx
        exact (ih _).mpr hx

theorem sentence_holds_iso {M N : FOL.Structure S} (e : M ≅ N) (p : FOL.Sentence S) :
    p.Holds M ↔ p.Holds N := by
  have hv : (fun i : Fin 0 => e.hom.map (p.ctx i) (i.elim0)) = (fun i => i.elim0) :=
    funext (fun i => i.elim0)
  have ht := holds_iso e p.formula (fun i => i.elim0)
  rw [hv] at ht
  exact ht

end Silmaril.Proofs.Logic.CommonLogic.ManySortedExpansion
