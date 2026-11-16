module

public import Silmaril.Logic.Rewriting.Thms
public import Silmaril.Logic.Reachability
public import Silmaril.Logic.Matching.FirstOrder.Algebraic

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Rewriting
open CategoryTheory Silmaril.Logic.Institution
variable {S : Type} {A B C : Algebraic.ManySorted.Signature S}

/-- The matching boundary excludes empty sorts; the EQ source above does not. -/
structure InhabitedModel (A : Algebraic.ManySorted.Signature S) where
  model : Model A
  nonempty : ∀ s, Nonempty (model.algebra.carrier s)

instance : Category (InhabitedModel A) where
  Hom M N := Model.Hom M.model N.model
  id M := Model.Hom.id M.model
  comp f g := Model.Hom.comp f g
  id_comp _ := Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ rfl)
  comp_id _ := Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ rfl)
  assoc _ _ _ := Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ rfl)

def inhabitedReduct (f : A ⟶ B) (M : InhabitedModel B) : InhabitedModel A :=
  ⟨reduct f M.model, M.nonempty⟩

def inhabitedReductFunctor (f : A ⟶ B) : InhabitedModel B ⥤ InhabitedModel A where
  obj := inhabitedReduct f
  map h := (reductFunctor f).map h
  map_id _ := Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ rfl)
  map_comp _ _ := Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ rfl)

private theorem inhabited_hom_hext {M M' N N' : InhabitedModel A}
    (hm : M = M') (hn : N = N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : HEq f.algebra.map g.algebra.map) : HEq f g := by
  cases hm; cases hn
  exact heq_of_eq (Model.Hom.ext _ _ (Algebraic.ManySorted.Model.Hom.ext _ _ (eq_of_heq h)))

theorem inhabitedReduct_id (M : InhabitedModel A) : inhabitedReduct (𝟙 A) M = M := by
  cases M with
  | mk M h => cases M; rfl

theorem inhabitedReduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : InhabitedModel C) :
    inhabitedReduct (f ≫ g) M = inhabitedReduct f (inhabitedReduct g M) := rfl

theorem inhabitedReductFunctor_id : inhabitedReductFunctor (𝟙 A) = 𝟭 (InhabitedModel A) := by
  apply Functor.hext inhabitedReduct_id
  intro M N h
  exact inhabited_hom_hext (inhabitedReduct_id M) (inhabitedReduct_id N) _ _ HEq.rfl

theorem inhabitedReductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    inhabitedReductFunctor (f ≫ g) = inhabitedReductFunctor g ⋙ inhabitedReductFunctor f := by
  apply Functor.hext (inhabitedReduct_comp f g)
  intro M N h
  exact inhabited_hom_hext (inhabitedReduct_comp f g M) (inhabitedReduct_comp f g N) _ _ HEq.rfl

inductive ReachOperation (A : Algebraic.ManySorted.Signature S) (cfg : S) :
    (n : Nat) → (Fin n → S) → S → Type where
  | base {n inputs output} : A.operations n inputs output → ReachOperation A cfg n inputs output
  | step : ReachOperation A cfg 1 (fun _ => cfg) cfg

abbrev reachSignature (A : Algebraic.ManySorted.Signature S) (cfg : S) : Reachability.Signature cfg :=
  ⟨⟨ReachOperation A cfg⟩, .step⟩

def reachMap (f : A ⟶ B) (cfg : S) : reachSignature A cfg ⟶ reachSignature B cfg where
  algebra := ⟨fun op => match op with | .base op => .base (f.operations op) | .step => .step⟩
  step := rfl

def termEmbedding (A : Algebraic.ManySorted.Signature S) (cfg : S) : A ⟶ (reachSignature A cfg).algebra :=
  ⟨ReachOperation.base⟩

/-- false chooses the discrete equality relation; true chooses directed rewriting.
Both are already reflexive/transitive, so finite closure has exactly that relation. -/
def selectedRelation (M : Model A) (directed : Bool) (s : S) :
    M.algebra.carrier s → M.algebra.carrier s → Prop :=
  if directed then M.reaches s else Eq

abbrev reachModel (M : InhabitedModel A) (cfg : S) (directed : Bool) :
    Reachability.Model cfg (reachSignature A cfg) where
  carrier := M.model.algebra.carrier
  nonempty := M.nonempty
  operation op args := match op with
    | .base op => {M.model.algebra.operation op args}
    | .step => {w | selectedRelation M.model directed cfg w (args 0)}

/-- Independent target sentences are arbitrary actual reachability sentences,
indexed by a configuration sort and the selected canonical relation. -/
abbrev CanonicalSentence (A : Algebraic.ManySorted.Signature S) :=
  (cfg : S) × Bool × Reachability.Sentence cfg (reachSignature A cfg)

def CanonicalSentence.map (f : A ⟶ B) (p : CanonicalSentence A) : CanonicalSentence B :=
  ⟨p.1, p.2.1, p.2.2.map p.1 (reachMap f p.1)⟩

def CanonicalSentence.Satisfies (M : InhabitedModel A) (p : CanonicalSentence A) : Prop :=
  p.2.2.Satisfies p.1 (reachModel M p.1 p.2.1)

abbrev compileEquation (e : Algebraic.ManySorted.Equation A) :
    Reachability.Sentence e.sort (reachSignature A e.sort) :=
  ⟨e.variableCount, e.context, .finite,
    Matching.FirstOrder.Pattern.ofTerm (e.lhs.map (termEmbedding A e.sort)),
    Matching.FirstOrder.Pattern.ofTerm (e.rhs.map (termEmbedding A e.sort))⟩

def compile : Sentence A → CanonicalSentence A
  | .equation e => ⟨e.sort, false, compileEquation e⟩
  | .rewrite e => ⟨e.sort, true, compileEquation e⟩

end Silmaril.Logic.Rewriting
