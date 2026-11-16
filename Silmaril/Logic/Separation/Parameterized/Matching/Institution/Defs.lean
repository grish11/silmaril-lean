module

public import Silmaril.Logic.Separation.Parameterized.Matching.Transport
public import Silmaril.Logic.Separation.Parameterized.FirstOrder.Institution.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.Parameterized.Matching.Canonical
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
namespace Native
open Silmaril.Logic.Matching

/-- Arbitrary native matching pattern pairs, not source formula wrappers.
Object variables range over the active value/heap carriers of the canonical
padded expansion. Native patterns may contain either μ or ν and tuple operations. -/
structure Pair (S : FOL.Signature) where
  contextSize : Nat
  profiles : Fin 0 → FirstOrderLFP.Profile S
  context : Fin contextSize → S.S
  pre : FixedPoint.Pattern (GuardedLFP.signature S).symbols (GuardedLFP.setContext profiles)
    (GuardedLFP.objContext context) (.base .truth)
  post : FixedPoint.Pattern (GuardedLFP.signature S).symbols (GuardedLFP.setContext profiles)
    (GuardedLFP.objContext context) (.base .truth)

def Pair.map {S T : FOL.Signature} (f : S ⟶ T) (p : Pair S) : Pair T :=
  ⟨p.contextSize,fun i => (p.profiles i).map f,f.sorts ∘ p.context,
    SortMaps.Hom.fixedPattern (GuardedLFP.signatureMap f) p.pre,
    SortMaps.Hom.fixedPattern (GuardedLFP.signatureMap f) p.post⟩

def Pair.Satisfies {S : FOL.Signature} (M : FirstOrderLFP.Model S) (p : Pair S) : Prop :=
  ∀ (θ : FirstOrderLFP.ObjEnv M p.context) (w : Unit),
    w ∈ p.pre.denote (GuardedLFP.rawExpansion M.toStructure) (fun i => some (θ i)) (fun i => i.elim0) →
    w ∈ p.post.denote (GuardedLFP.rawExpansion M.toStructure) (fun i => some (θ i)) (fun i => i.elim0)

private theorem fixedPattern_heq {A B : SortMaps.Signature}
    {f g : SortMaps.Hom A B} (h : f = g)
    {r k} {P : Fin r → A.sorts} {Γ : Fin k → A.sorts} {s}
    (p : FixedPoint.Pattern A.symbols P Γ s) :
    HEq (f.fixedPattern p) (g.fixedPattern p) := by
  cases h
  rfl

theorem Pair.map_id {S : FOL.Signature} (p : Pair S) : p.map (𝟙 S) = p := by
  cases p with
  | mk k P Γ pre post =>
    unfold map
    congr 1
    · exact eq_of_heq ((fixedPattern_heq (GuardedLFP.signatureMap_id S) pre).trans
        (heq_of_eq (SortMaps.Hom.fixedPattern_id pre)))
    · exact eq_of_heq ((fixedPattern_heq (GuardedLFP.signatureMap_id S) post).trans
        (heq_of_eq (SortMaps.Hom.fixedPattern_id post)))

theorem Pair.map_comp {S T U : FOL.Signature} (f : S ⟶ T) (g : T ⟶ U) (p : Pair S) :
    p.map (f ≫ g) = (p.map f).map g := by
  cases p with
  | mk k P Γ pre post =>
    unfold map
    congr 1
    · exact eq_of_heq ((fixedPattern_heq (GuardedLFP.signatureMap_comp f g) pre).trans
        (heq_of_eq (SortMaps.Hom.fixedPattern_comp _ _ pre)))
    · exact eq_of_heq ((fixedPattern_heq (GuardedLFP.signatureMap_comp f g) post).trans
        (heq_of_eq (SortMaps.Hom.fixedPattern_comp _ _ post)))

private theorem denote_model_heq {S : Type} {A : Algebraic.ManySorted.Signature S}
    {r k} {P : Fin r → S} {Γ : Fin k → S} {s}
    (p : FixedPoint.Pattern A P Γ s) {M N : FirstOrder.Model A} (hm : M = N)
    {v : FixedPoint.ObjEnv A M Γ} {v' : FixedPoint.ObjEnv A N Γ} (hv : HEq v v')
    {η : FixedPoint.SetEnv A M P} {η' : FixedPoint.SetEnv A N P} (hη : HEq η η') :
    HEq (p.denote M v η) (p.denote N v' η') := by
  cases hm
  cases hv
  cases hη
  rfl

theorem Pair.satisfaction {S T : FOL.Signature} (f : S ⟶ T) (M : FirstOrderLFP.Model T) (p : Pair S) :
    (p.map f).Satisfies M ↔ p.Satisfies ((FirstOrderLFP.reduct f).obj M) := by
  have hp : ∀ (θ : FirstOrderLFP.ObjEnv ((FirstOrderLFP.reduct f).obj M) p.context),
      (SortMaps.Hom.fixedPattern (GuardedLFP.signatureMap f) p.pre).denote
          (GuardedLFP.rawExpansion M.toStructure) (fun i => some (θ i)) (fun i => i.elim0) =
      p.pre.denote (GuardedLFP.rawExpansion ((FOL.Structure.reduct f).obj M.toStructure))
        (fun i => some (θ i)) (fun i => i.elim0) := by
    intro θ
    have ht := congrArg (fun F => F (fun i => i.elim0))
      (SortMaps.Hom.denote_fixedPattern (GuardedLFP.signatureMap f)
        (GuardedLFP.rawExpansion M.toStructure) p.pre (fun i => some (θ i)))
    exact ht.trans (eq_of_heq (denote_model_heq p.pre (expansion_reduct f M.toStructure) HEq.rfl HEq.rfl))
  have hq : ∀ (θ : FirstOrderLFP.ObjEnv ((FirstOrderLFP.reduct f).obj M) p.context),
      (SortMaps.Hom.fixedPattern (GuardedLFP.signatureMap f) p.post).denote
          (GuardedLFP.rawExpansion M.toStructure) (fun i => some (θ i)) (fun i => i.elim0) =
      p.post.denote (GuardedLFP.rawExpansion ((FOL.Structure.reduct f).obj M.toStructure))
        (fun i => some (θ i)) (fun i => i.elim0) := by
    intro θ
    have ht := congrArg (fun F => F (fun i => i.elim0))
      (SortMaps.Hom.denote_fixedPattern (GuardedLFP.signatureMap f)
        (GuardedLFP.rawExpansion M.toStructure) p.post (fun i => some (θ i)))
    exact ht.trans (eq_of_heq (denote_model_heq p.post (expansion_reduct f M.toStructure) HEq.rfl HEq.rfl))
  constructor
  · intro h θ w hw
    exact (hq θ) ▸ h θ w ((hp θ).symm ▸ hw)
  · intro h θ w hw
    exact (hq θ).symm ▸ h θ w ((hp θ) ▸ hw)

end Native
variable {A B C : Signature}
abbrev Sentence (A : Signature) := Native.Pair (FirstOrder.signature A)
abbrev Sentence.map (f : A ⟶ B) (p : Sentence A) : Sentence B := Native.Pair.map (FirstOrder.signatureMap f) p
abbrev Sentence.Satisfies (M : Model A) (p : Sentence A) := Native.Pair.Satisfies (FirstOrder.model M) p

theorem Sentence.map_id (p : Sentence A) : Sentence.map (𝟙 A) p = p := by
  change Native.Pair.map (FirstOrder.signatureMap (𝟙 A)) p = p
  rw [FirstOrder.signatureMap_id]
  exact Native.Pair.map_id p

theorem Sentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    Sentence.map (f ≫ g) p = Sentence.map g (Sentence.map f p) := by
  change Native.Pair.map (FirstOrder.signatureMap (f ≫ g)) p = _
  rw [FirstOrder.signatureMap_comp,Native.Pair.map_comp]

theorem Sentence.satisfaction (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    Sentence.Satisfies M (Sentence.map f p) ↔ Sentence.Satisfies (reduct f M) p := by
  change Native.Pair.Satisfies (FirstOrder.model M) (Native.Pair.map (FirstOrder.signatureMap f) p) ↔
    Native.Pair.Satisfies (FirstOrder.model (reduct f M)) p
  rw [Native.Pair.satisfaction]
  exact Iff.of_eq (congrArg (fun N => Native.Pair.Satisfies N p) (FirstOrder.model_reduct f M))

/-- Actual native matching semantics on canonical padded resource models, with
all source value/resource homomorphisms. The active-assignment entailment
interface is distinct from unrestricted raw matching validity and from the
existing guarded institution's equality-only model category. -/
def institution : Signature ⥤ Room where
  obj A := ⟨Sentence A,Cat.of (Model A),Sentence.Satisfies⟩
  map f := ⟨Sentence.map f,reductFunctor f,Sentence.satisfaction f⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id) reductFunctor_id
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) (reductFunctor_comp f g)

def inst : Inst := ⟨Signature,institution⟩

end Silmaril.Logic.Separation.Parameterized.Matching.Canonical
