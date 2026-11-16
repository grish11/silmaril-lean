module

public import Silmaril.Proofs.Logic.Separation.Matching

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation
open CategoryTheory Silmaril.Logic.Institution
variable {A B C : Signature}

theorem matchingMap_id (A : Signature) : matchingMap (𝟙 A) = 𝟙 (matchingSignature A) := by
  apply Algebraic.ManySorted.Signature.Hom.ext
  intro n inputs output op
  cases op <;> rfl

theorem matchingMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    matchingMap (f ≫ g) = matchingMap f ≫ matchingMap g := by
  apply Algebraic.ManySorted.Signature.Hom.ext
  intro n inputs output op
  cases op <;> rfl

theorem matchingModel_reduct (f : A ⟶ B) (M : Model B) :
    matchingModel (reduct f M) = Matching.FirstOrder.SignatureMap.reduct (matchingMap f) (matchingModel M) := by
  unfold matchingModel Matching.FirstOrder.SignatureMap.reduct
  congr 1
  funext n inputs output op args
  cases op <;> rfl

/-- Resource homomorphisms induce actual native matching model arrows. -/
def matchingModelFunctor (A : Signature) : Model A ⥤ Matching.FirstOrder.Model (matchingSignature A) where
  obj := matchingModel
  map f :=
    { map := fun _ => f.map
      operation := by
        intro n inputs output op args h hh
        cases op with
        | atom a => exact f.atom a hh
        | emp => exact (congrArg f.map hh).trans f.unit
        | join => exact f.join hh
        | extension => exact f.join hh }
  map_id _ := Matching.FirstOrder.Model.Hom.ext _ _ rfl
  map_comp _ _ := Matching.FirstOrder.Model.Hom.ext _ _ rfl

theorem compileBase_map (f : A ⟶ B) (p : Assertion A) :
    (compileBase p).map (matchingMap f) = compileBase (p.map f) := by
  induction p with
  | atom a => exact congrArg (Matching.FirstOrder.Pattern.app (A := matchingSignature B) (MatchingOperation.atom (A := B) (f a))) (funext fun i => i.elim0)
  | emp => exact congrArg (Matching.FirstOrder.Pattern.app (A := matchingSignature B) (MatchingOperation.emp (A := B))) (funext fun i => i.elim0)
  | neg p hp => exact congrArg Matching.FirstOrder.Pattern.neg hp
  | conj p q hp hq => exact congrArg₂ Matching.FirstOrder.Pattern.conj hp hq
  | sep p q hp hq =>
      exact congrArg (Matching.FirstOrder.Pattern.app (A := matchingSignature B) (MatchingOperation.join (A := B))) (funext fun i => Fin.cases hp (fun _ => hq) i)
  | wand p q hp hq =>
      exact congrArg Matching.FirstOrder.Pattern.neg (congrArg (Matching.FirstOrder.Pattern.app (A := matchingSignature B) (MatchingOperation.extension (A := B)))
        (funext fun i => Fin.cases hp (fun _ => congrArg Matching.FirstOrder.Pattern.neg hq) i))

theorem compilePattern_map (f : A ⟶ B) {r} (p : Pattern A r) :
    (compilePattern p).map (matchingMap f) = compilePattern (p.map f) := by
  induction p with
  | base p => exact congrArg Matching.FixedPoint.Pattern.base (compileBase_map f p)
  | var => rfl
  | conj p q hp hq => exact congrArg₂ Matching.FixedPoint.Pattern.conj hp hq
  | disj p q hp hq => exact congrArg₂ Matching.FixedPoint.Pattern.disj hp hq
  | sep p q hp hq =>
      exact congrArg (Matching.FixedPoint.Pattern.app (A := matchingSignature B) (MatchingOperation.join (A := B))) (funext fun i => Fin.cases hp (fun _ => hq) i)
  | wand p q hq =>
      exact congrArg (Matching.FixedPoint.Pattern.dualApp (A := matchingSignature B) (MatchingOperation.extension (A := B)))
        (funext fun i => Fin.cases
          (congrArg Matching.FixedPoint.Pattern.base (congrArg Matching.FirstOrder.Pattern.neg (compileBase_map f p)))
          (fun _ => hq) i)
  | mu p hp => exact congrArg Matching.FixedPoint.Pattern.mu hp

private theorem dual_map {X Y : Algebraic.ManySorted.Signature Unit} (f : X ⟶ Y)
    {r k} {P : Fin r → Unit} {Γ : Fin k → Unit} {s}
    (p : Matching.FixedPoint.Pattern X P Γ s) : p.dual.map f = (p.map f).dual := by
  induction p with
  | base => rfl
  | setvar => rfl
  | app op args ih => exact congrArg (Matching.FixedPoint.Pattern.dualApp _) (funext ih)
  | dualApp op args ih => exact congrArg (Matching.FixedPoint.Pattern.app _) (funext ih)
  | conj p q hp hq => exact congrArg₂ Matching.FixedPoint.Pattern.disj hp hq
  | disj p q hp hq => exact congrArg₂ Matching.FixedPoint.Pattern.conj hp hq
  | ex s p hp => exact congrArg (Matching.FixedPoint.Pattern.all s) hp
  | all s p hp => exact congrArg (Matching.FixedPoint.Pattern.ex s) hp
  | mu p hp => exact congrArg Matching.FixedPoint.Pattern.nu hp
  | nu p hp => exact congrArg Matching.FixedPoint.Pattern.mu hp

theorem encode_map (f : A ⟶ B) (p : Sentence A) :
    (encode p).map (matchingMap f) = encode (p.map f) := by
  change Matching.FixedPoint.Sentence.mk 0 0 _ _ _ _ = Matching.FixedPoint.Sentence.mk 0 0 _ _ _ _
  congr 1
  change Matching.FixedPoint.Pattern.disj
    ((compilePattern p.pre).dual.map (matchingMap f)) ((compilePattern p.post).map (matchingMap f)) =
    Matching.FixedPoint.Pattern.disj (compilePattern (p.pre.map f)).dual (compilePattern (p.post.map f))
  rw [dual_map, compilePattern_map, compilePattern_map]

/-- All target sentences are actual matching sentences; models are precisely
resource-generated interpretations, not arbitrary set-valued matching models. -/
def canonicalInstitution : Signature ⥤ Room where
  obj A := ⟨Matching.FixedPoint.Sentence (matchingSignature A), Cat.of (Model A),
    fun M p => p.Satisfies (matchingModel M)⟩
  map f := ⟨Matching.FixedPoint.Sentence.map (matchingMap f), reductFunctor f, by
    intro M p
    change (p.map (matchingMap f)).Satisfies (matchingModel M) ↔ _
    have hs : (p.map (matchingMap f)).Satisfies (matchingModel M) ↔
        p.Satisfies (Matching.FirstOrder.SignatureMap.reduct (matchingMap f) (matchingModel M)) :=
      ((Matching.FixedPoint.institution Unit).map (matchingMap f)).sat (matchingModel M) p
    rw [← matchingModel_reduct] at hs
    exact hs⟩
  map_id A := Room.hom_ext (by
    funext p
    change p.map (matchingMap (𝟙 A)) = p
    rw [matchingMap_id]
    exact Matching.FixedPoint.Sentence.map_id p) reductFunctor_id
  map_comp f g := Room.hom_ext (by
    funext p
    change p.map (matchingMap (f ≫ g)) = (p.map (matchingMap f)).map (matchingMap g)
    rw [matchingMap_comp]
    exact Matching.FixedPoint.Sentence.map_comp _ _ p) (reductFunctor_comp f g)

def toCanonicalMatchingNat : institution ⟶ canonicalInstitution where
  app _ := ⟨encode, 𝟭 _, encode_satisfaction⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p; exact (encode_map f p).symm
    · rfl

def canonicalInst : Inst := ⟨Signature, canonicalInstitution⟩
def toCanonicalMatching : Inst.CoHom recursiveInst canonicalInst where
  Φ := 𝟭 _
  ρ := toCanonicalMatchingNat ≫ (Functor.leftUnitor canonicalInstitution).inv

theorem toCanonicalMatching_modelExpansive : toCanonicalMatching.ModelExpansive := fun _ M => ⟨M, rfl⟩

theorem toCanonicalMatching_entails_iff (A : Signature) (H : Set (Sentence A)) (p : Sentence A) :
    (institution.obj A).Entails H p ↔ (canonicalInstitution.obj A).Entails (encode '' H) (encode p) :=
  toCanonicalMatching.entails_iff toCanonicalMatching_modelExpansive A H p

end Silmaril.Logic.Separation
