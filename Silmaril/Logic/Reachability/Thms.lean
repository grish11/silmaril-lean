module

public import Silmaril.Proofs.Logic.Reachability.Semantics

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Reachability
open CategoryTheory Silmaril.Logic.Institution
variable {S : Type} (cfg : S) {A B C : Signature cfg}

/-- In the unconditional fragment, 2013 Definition 7 is exactly the one-path mode:
termination is absence of an actual infinite execution. -/
theorem onePath_iff_terminating {W : Type} (R : W → W → Prop) (Q : W → Prop) (w : W) :
    Mode.onePath.Holds R Q w ↔ (¬ Diverges R w → Reaches R Q w) := by
  classical
  change (Reaches R Q w ∨ Diverges R w) ↔ _
  exact or_iff_not_imp_right

/-- A terminal configuration must satisfy the target even for partial correctness. -/
theorem allPartial_deadlock {W : Type} (R : W → W → Prop) (Q : W → Prop) (w : W)
    (hd : ∀ v, ¬ R w v) : AllPartial R Q w ↔ Q w := by
  constructor
  · intro h
    obtain ⟨i, _, hq⟩ := h 0 (fun _ => w) rfl
      (fun _ hi => (Nat.not_lt_zero _ hi).elim) hd
    exact hq
  · intro hq n path h0 _ _
    exact ⟨0, Nat.zero_le n, h0.symm ▸ hq⟩

theorem step_reduct (f : A ⟶ B) (M : Model cfg B) :
    step cfg (Matching.FirstOrder.SignatureMap.reduct f.algebra M) = step cfg M := by
  funext w v
  change (w ∈ M.operation (f.algebra.operations A.step) (fun _ => v)) = _
  rw [f.step]
  rfl

theorem Sentence.map_id (p : Sentence cfg A) : p.map cfg (𝟙 A) = p := by
  cases p with
  | mk k Γ mode pre post =>
      change Sentence.mk k Γ mode (pre.map (𝟙 A.algebra)) (post.map (𝟙 A.algebra)) = _
      rw [Matching.FirstOrder.Pattern.map_id, Matching.FirstOrder.Pattern.map_id]

theorem Sentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence cfg A) :
    p.map cfg (f ≫ g) = (p.map cfg f).map cfg g := by
  cases p with
  | mk k Γ mode pre post =>
      change Sentence.mk k Γ mode (pre.map (f.algebra ≫ g.algebra)) (post.map (f.algebra ≫ g.algebra)) = _
      rw [Matching.FirstOrder.Pattern.map_comp, Matching.FirstOrder.Pattern.map_comp]
      rfl

theorem Sentence.satisfaction (f : A ⟶ B) (M : Model cfg B) (p : Sentence cfg A) :
    (p.map cfg f).Satisfies cfg M ↔
      p.Satisfies cfg (Matching.FirstOrder.SignatureMap.reduct f.algebra M) := by
  simp only [Sentence.Satisfies, Sentence.map, Matching.FirstOrder.SignatureMap.denote_map,
    step_reduct]
  rfl

def institution : Signature cfg ⥤ Room where
  obj A := ⟨Sentence cfg A, Cat.of (Model cfg A), Sentence.Satisfies cfg⟩
  map f := ⟨Sentence.map cfg f, Matching.FirstOrder.SignatureMap.reductFunctor f.algebra,
    Sentence.satisfaction cfg f⟩
  map_id _ := Room.hom_ext (funext (Sentence.map_id cfg)) Matching.FirstOrder.SignatureMap.reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp cfg f g))
    (Matching.FirstOrder.SignatureMap.reductFunctor_comp f.algebra g.algebra)

/-- The institution as a bundled `Inst`: its signatures and room functor `institution`, named so
that records and comorphisms can refer to it. -/
def inst := (⟨Signature cfg, institution cfg⟩ : Silmaril.Logic.Institution.Inst)

/-- Duality commutes with signature maps, including fixed-point binders. -/
theorem dual_map {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    {X Y : Algebraic.ManySorted.Signature S} (f : X ⟶ Y)
    (p : Matching.FixedPoint.Pattern X P Γ s) :
    p.dual.map f = (p.map f).dual := by
  induction p with
  | base => rfl
  | setvar => rfl
  | app op args ih => exact congrArg (Matching.FixedPoint.Pattern.dualApp _) (funext ih)
  | dualApp op args ih => exact congrArg (Matching.FixedPoint.Pattern.app _) (funext ih)
  | conj p q hp hq => exact congrArg₂ Matching.FixedPoint.Pattern.disj hp hq
  | disj p q hp hq => exact congrArg₂ Matching.FixedPoint.Pattern.conj hp hq
  | ex bound p hp => exact congrArg (Matching.FixedPoint.Pattern.all bound) hp
  | all bound p hp => exact congrArg (Matching.FixedPoint.Pattern.ex bound) hp
  | mu p hp => exact congrArg Matching.FixedPoint.Pattern.nu hp
  | nu p hp => exact congrArg Matching.FixedPoint.Pattern.mu hp

theorem encode_map (f : A ⟶ B) (p : Sentence cfg A) :
    encode cfg (p.map cfg f) = (encode cfg p).map f.algebra := by
  have hs : f.algebra.operations A.step = B.step := f.step
  cases p with
  | mk k Γ mode pre post =>
      cases mode <;>
        simp only [encode, outcomePattern, reachPattern, divergePattern, badPattern,
          Sentence.map, Matching.FixedPoint.Sentence.map, Matching.FixedPoint.Pattern.map,
          Matching.FirstOrder.Pattern.map, Matching.FixedPoint.Pattern.dual, hs]
      rfl

def matchingNatural : institution cfg ⟶ signatures cfg ⋙ Matching.FixedPoint.institution S where
  app A := ⟨encode cfg, 𝟭 (Model cfg A), encode_correct⟩
  naturality := by
    intro A B f
    exact Room.hom_ext (funext (encode_map cfg f)) rfl

/-- Genuine global comorphism, retaining actual matching carriers, operations and homomorphisms. -/
def toMatching : Inst.CoHom ⟨Signature cfg, institution cfg⟩
    ⟨Algebraic.ManySorted.Signature S, Matching.FixedPoint.institution S⟩ :=
  ⟨signatures cfg, matchingNatural cfg⟩

theorem toMatching_modelExpansive : (toMatching cfg).ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem entails_iff (A : Signature cfg) (H : Set (Sentence cfg A)) (p : Sentence cfg A) :
    ((institution cfg).obj A).Entails H p ↔
      ((Matching.FixedPoint.institution S).obj A.algebra).Entails (encode cfg '' H) (encode cfg p) :=
  (toMatching cfg).entails_iff (toMatching_modelExpansive cfg) A H p

end Silmaril.Logic.Reachability
