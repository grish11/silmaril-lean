module

public import Silmaril.Proofs.Logic.Rewriting.TermDenotation

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Rewriting
open CategoryTheory Silmaril.Logic.Institution
variable {S : Type} {A B C : Algebraic.ManySorted.Signature S}

theorem selectedRelation_refl (M : Model A) (d : Bool) (s : S) (w : M.algebra.carrier s) :
    selectedRelation M d s w w := by cases d <;> simp [selectedRelation, M.refl]

theorem selectedRelation_trans (M : Model A) (d : Bool) (s : S) {x y z : M.algebra.carrier s}
    (h : selectedRelation M d s x y) (k : selectedRelation M d s y z) :
    selectedRelation M d s x z := by
  cases d
  · exact h.trans k
  · exact M.trans s h k

theorem reaches_selected_iff (M : Model A) (d : Bool) (s : S) (x y : M.algebra.carrier s) :
    Reachability.Reaches (selectedRelation M d s) (fun z => z = y) x ↔ selectedRelation M d s x y := by
  constructor
  · intro h
    induction h with
    | now h => cases h; exact selectedRelation_refl M d s _
    | next _ h _ ih => exact selectedRelation_trans M d s h ih
  · intro h
    exact .next trivial h (.now rfl)

theorem compileEquation_satisfaction (M : InhabitedModel A) (e : Algebraic.ManySorted.Equation A) (d : Bool) :
    (compileEquation e).Satisfies e.sort (reachModel M e.sort d) ↔
      ∀ v, selectedRelation M.model d e.sort (M.model.algebra.eval v e.lhs) (M.model.algebra.eval v e.rhs) := by
  change (∀ v w, w ∈ (reachModel M e.sort d).denote v
      (Matching.FirstOrder.Pattern.ofTerm (e.lhs.map (termEmbedding A e.sort))) →
    Reachability.Reaches (selectedRelation M.model d e.sort)
      (fun x => x ∈ (reachModel M e.sort d).denote v
        (Matching.FirstOrder.Pattern.ofTerm (e.rhs.map (termEmbedding A e.sort)))) w) ↔ _
  simp only [denote_term, Set.mem_singleton_iff, reaches_selected_iff]
  constructor
  · intro h v; exact h v _ rfl
  · intro h v w hw; exact hw ▸ h v

theorem compile_satisfaction (M : InhabitedModel A) (p : Sentence A) :
    CanonicalSentence.Satisfies M (compile p) ↔ Sentence.Satisfies M.model p := by
  cases p with
  | equation e => exact compileEquation_satisfaction M e false
  | rewrite e => exact compileEquation_satisfaction M e true


theorem reachMap_id (A : Algebraic.ManySorted.Signature S) (cfg : S) :
    reachMap (𝟙 A) cfg = 𝟙 (reachSignature A cfg) := by
  apply Reachability.Signature.Hom.ext
  apply Algebraic.ManySorted.Signature.Hom.ext
  intro n inputs output op
  cases op <;> rfl

theorem reachMap_comp (f : A ⟶ B) (g : B ⟶ C) (cfg : S) :
    reachMap (f ≫ g) cfg = reachMap f cfg ≫ reachMap g cfg := by
  apply Reachability.Signature.Hom.ext
  apply Algebraic.ManySorted.Signature.Hom.ext
  intro n inputs output op
  cases op <;> rfl

theorem CanonicalSentence.map_id (p : CanonicalSentence A) : p.map (𝟙 A) = p := by
  rcases p with ⟨cfg, d, p⟩
  simp only [map, reachMap_id, Reachability.Sentence.map_id]

theorem CanonicalSentence.map_comp (f : A ⟶ B) (g : B ⟶ C) (p : CanonicalSentence A) :
    p.map (f ≫ g) = (p.map f).map g := by
  rcases p with ⟨cfg, d, p⟩
  simp only [map, reachMap_comp, Reachability.Sentence.map_comp]

theorem reachModel_reduct (f : A ⟶ B) (M : InhabitedModel B) (cfg : S) (d : Bool) :
    reachModel (inhabitedReduct f M) cfg d =
      Matching.FirstOrder.SignatureMap.reduct (reachMap f cfg).algebra (reachModel M cfg d) := by
  unfold reachModel Matching.FirstOrder.SignatureMap.reduct
  congr 1
  funext n inputs output op args
  cases op <;> rfl

theorem CanonicalSentence.satisfaction (f : A ⟶ B) (M : InhabitedModel B) (p : CanonicalSentence A) :
    Satisfies M (p.map f) ↔ Satisfies (inhabitedReduct f M) p := by
  rcases p with ⟨cfg, d, p⟩
  change (p.map cfg (reachMap f cfg)).Satisfies cfg (reachModel M cfg d) ↔ _
  rw [Reachability.Sentence.satisfaction, ← reachModel_reduct]
  rfl

def inhabitedInstitution (S : Type) : Algebraic.ManySorted.Signature S ⥤ Room where
  obj A := ⟨Sentence A, Cat.of (InhabitedModel A), fun M p => Sentence.Satisfies M.model p⟩
  map f := ⟨Sentence.map f, inhabitedReductFunctor f, fun M p => Sentence.satisfaction f M.model p⟩
  map_id _ := Room.hom_ext (funext Sentence.map_id) inhabitedReductFunctor_id
  map_comp f g := Room.hom_ext (funext (Sentence.map_comp f g)) (inhabitedReductFunctor_comp f g)

/-- A family of actual reachability rooms, restricted to generated models. -/
def canonicalInstitution (S : Type) : Algebraic.ManySorted.Signature S ⥤ Room where
  obj A := ⟨CanonicalSentence A, Cat.of (InhabitedModel A), CanonicalSentence.Satisfies⟩
  map f := ⟨CanonicalSentence.map f, inhabitedReductFunctor f, CanonicalSentence.satisfaction f⟩
  map_id _ := Room.hom_ext (funext CanonicalSentence.map_id) inhabitedReductFunctor_id
  map_comp f g := Room.hom_ext (funext (CanonicalSentence.map_comp f g)) (inhabitedReductFunctor_comp f g)

theorem term_compile_map (f : A ⟶ B) (cfg : S) {k} {Γ : Fin k → S} {s}
    (t : Algebraic.ManySorted.Term A Γ s) :
    Matching.FirstOrder.Pattern.map (reachMap f cfg).algebra
      (Matching.FirstOrder.Pattern.ofTerm (t.map (termEmbedding A cfg))) =
      Matching.FirstOrder.Pattern.ofTerm ((t.map f).map (termEmbedding B cfg)) := by
  induction t with
  | var => rfl
  | app op args ih => exact congrArg (Matching.FirstOrder.Pattern.app _) (funext ih)

theorem compile_map (f : A ⟶ B) (p : Sentence A) :
    (compile p).map f = compile (p.map f) := by
  cases p with
  | equation e =>
      dsimp only [compile, Sentence.map, CanonicalSentence.map, compileEquation,
        Reachability.Sentence.map, Algebraic.ManySorted.Equation.map]
      rw [term_compile_map, term_compile_map]
  | rewrite e =>
      dsimp only [compile, Sentence.map, CanonicalSentence.map, compileEquation,
        Reachability.Sentence.map, Algebraic.ManySorted.Equation.map]
      rw [term_compile_map, term_compile_map]

def toCanonicalReachabilityNat (S : Type) : inhabitedInstitution S ⟶ canonicalInstitution S where
  app A := ⟨compile, 𝟭 _, compile_satisfaction⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · funext p; exact (compile_map f p).symm
    · rfl

def inhabitedInst (S : Type) : Inst := ⟨Algebraic.ManySorted.Signature S, inhabitedInstitution S⟩
def canonicalInst (S : Type) : Inst := ⟨Algebraic.ManySorted.Signature S, canonicalInstitution S⟩

def toCanonicalReachability (S : Type) : Inst.CoHom (inhabitedInst S) (canonicalInst S) where
  Φ := 𝟭 _
  ρ := toCanonicalReachabilityNat S ≫ (Functor.leftUnitor (canonicalInstitution S)).inv

theorem toCanonicalReachability_modelExpansive (S : Type) :
    (toCanonicalReachability S).ModelExpansive := fun _ M => ⟨M, rfl⟩

def forgetInhabited (A : Algebraic.ManySorted.Signature S) : InhabitedModel A ⥤ Model A where
  obj M := M.model
  map h := h

def restrictInhabitedNat (S : Type) : institution S ⟶ inhabitedInstitution S where
  app A := ⟨id, forgetInhabited A, fun _ _ => Iff.rfl⟩
  naturality := by
    intro A B f
    apply Room.hom_ext
    · rfl
    · rfl

def restrictInhabited (S : Type) : Inst.CoHom (rewritingInst S) (inhabitedInst S) where
  Φ := 𝟭 _
  ρ := restrictInhabitedNat S ≫ (Functor.leftUnitor (inhabitedInstitution S)).inv

theorem toCanonicalReachability_entails_iff (S : Type) (A : Algebraic.ManySorted.Signature S)
    (H : Set (Sentence A)) (p : Sentence A) :
    ((inhabitedInstitution S).obj A).Entails H p ↔
      ((canonicalInstitution S).obj A).Entails (compile '' H) (compile p) :=
  (toCanonicalReachability S).entails_iff (toCanonicalReachability_modelExpansive S) A H p

end Silmaril.Logic.Rewriting
