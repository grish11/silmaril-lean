module

public import Silmaril.Logic.Matching.GuardedFOL.Expansion
public import Silmaril.Proofs.Logic.Matching.GuardedFOL.Semantics

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

theorem unpad_op (M : FOL.Structure S) {n inputs output} (op : S.Op n inputs output)
    (args : ∀ i, (decode (expand M)).carrier (inputs i)) :
    unpad ((decode (expand M)).op op args) = M.op op (fun i => unpad (args i)) := by
  have member : ((decode (expand M)).op op args).val ∈
      (expand M).base.operation (.function op) (fun i => (args i).val) := by
    rw [function_graph (expand M)]
    rfl
  rcases member with ⟨values, hv, ho⟩
  have same : values = fun i => unpad (args i) := by
    funext i
    exact Option.some.inj ((hv i).symm.trans (unpad_spec (args i)).symm)
  apply Option.some.inj
  exact (unpad_spec _).trans (ho.trans (congrArg (fun vs => some (M.op op vs)) same))

theorem unpad_rel (M : FOL.Structure S) {n inputs} (r : S.Rel n inputs)
    (args : ∀ i, (decode (expand M)).carrier (inputs i)) :
    (decode (expand M)).rel r args ↔ M.rel r (fun i => unpad (args i)) := by
  change (expand M).base.operation (.relation r) (fun i => (args i).val) = Set.univ ↔ _
  rw [← relation_member (expand M) r (fun i => (args i).val) ()]
  constructor
  · rintro ⟨values, hv, hr⟩
    have same : values = fun i => unpad (args i) := by
      funext i
      exact Option.some.inj ((hv i).symm.trans (unpad_spec (args i)).symm)
    exact same ▸ hr
  · intro hr
    exact ⟨_, fun i => (unpad_spec (args i)).symm, hr⟩

private theorem structureHom_ext {M N : FOL.Structure S} (f g : M ⟶ N) (h : f.map = g.map) : f = g := by
  cases f; cases g; cases h; rfl

/-- An actual isomorphism in the public category of FOL structures. -/
def decodeExpansionIso (M : FOL.Structure S) : decode (expand M) ≅ M where
  hom := ⟨fun _ => unpad, unpad_op M, fun r args h => (unpad_rel M r args).mp h⟩
  inv := {
    map := fun s => (activeEquiv M s).symm
    map_op := by
      intro n inputs output op args
      apply (activeEquiv M output).injective
      change unpad ((activeEquiv M output).symm (M.op op args)) =
        unpad ((decode (expand M)).op op (fun i => (activeEquiv M (inputs i)).symm (args i)))
      rw [unpad_op M]
      exact (activeEquiv M output).apply_symm_apply _ |>.trans
        (congrArg (M.op op) (funext fun i => (activeEquiv M (inputs i)).apply_symm_apply (args i))).symm
    map_rel := by
      intro n inputs r args hr
      apply (unpad_rel M r _).mpr
      simpa only [show (fun i => unpad ((activeEquiv M (inputs i)).symm (args i))) = args from
        funext fun i => (activeEquiv M (inputs i)).apply_symm_apply (args i)] using hr }
  hom_inv_id := by
    apply structureHom_ext
    funext s x
    exact (activeEquiv M s).symm_apply_apply x
  inv_hom_id := by
    apply structureHom_ext
    funext s x
    exact (activeEquiv M s).apply_symm_apply x

/-- Evaluation commutes with actual FOL structure homomorphisms. -/
theorem eval_hom {M N : FOL.Structure S} (f : M ⟶ N) {k : Nat} {Γ : Fin k → S.S}
    {s : S.S} (t : EQ.Term S.toSignature Γ s) (v : ∀ i, M.carrier (Γ i)) :
    f.map s (t.eval M.toAlgebra v) = t.eval N.toAlgebra (fun i => f.map (Γ i) (v i)) := by
  induction t with
  | var => rfl
  | app op args ih =>
      change f.map _ (M.op op _) = N.op op _
      rw [f.map_op]
      exact congrArg (N.op op) (funext ih)

def carrierEquiv {M N : FOL.Structure S} (e : M ≅ N) (s : S.S) : M.carrier s ≃ N.carrier s where
  toFun := e.hom.map s
  invFun := e.inv.map s
  left_inv x := congrArg (fun f : M ⟶ M => f.map s x) e.hom_inv_id
  right_inv x := congrArg (fun f : N ⟶ N => f.map s x) e.inv_hom_id

/-- Formula truth transport is proved through the actual structure isomorphism. -/
theorem holds_iso {M N : FOL.Structure S} (e : M ≅ N) {k : Nat} {Γ : Fin k → S.S}
    (p : FOL.Formula S Γ) : ∀ v,
    p.Holds M v ↔ p.Holds N (fun i => e.hom.map (Γ i) (v i)) := by
  induction p with
  | eq t u =>
      intro v
      change t.eval M.toAlgebra v = u.eval M.toAlgebra v ↔
        t.eval N.toAlgebra (fun i => e.hom.map _ (v i)) = u.eval N.toAlgebra (fun i => e.hom.map _ (v i))
      rw [← eval_hom e.hom t v, ← eval_hom e.hom u v]
      exact (carrierEquiv e _).injective.eq_iff.symm
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
            (fun i => (args i).eval M.toAlgebra v) := funext fun i => (carrierEquiv e _).left_inv _
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
        obtain ⟨x, rfl⟩ := (carrierEquiv e (Δ 0)).surjective y
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
end Silmaril.Logic.Matching.GuardedFOL
