module

public import Silmaril.Logic.Institution.Basic

@[expose] public section

/-! # Generalized institution evaluation

Use the sentence and model functors of a classic institution. The value of an
individual model and sentence is separate from consequence over a class of models.
-/

namespace Silmaril.Logic.Institution.Generalized

open CategoryTheory Opposite

universe u v w m₁ m₂ d c

/-- The data common to exact and order-lax evaluations. -/
structure Evaluation (Sign : Type u) [Category.{v} Sign] (D : Type d) where
  /-- Covariant sentence translation. -/
  Sen : Sign ⥤ Type w
  /-- Contravariant reduction of model categories. -/
  Mod : Signᵒᵖ ⥤ Cat.{m₁, m₂}
  /-- The value of a sentence in a single model. -/
  eval : (S : Sign) → Mod.obj (op S) → Sen.obj S → D

variable {Sign : Type u} [Category.{v} Sign] {D : Type d}

namespace Evaluation

variable (E : Evaluation.{u,v,w,m₁,m₂,d} Sign D)

/-- Models of a premise set under a chosen predicate on values. -/
def modelsOf {S : Sign} (accepts : D → Prop) (Γ : Set (E.Sen.obj S)) :
    Set (E.Mod.obj (op S)) :=
  {M | ∀ φ ∈ Γ, accepts (E.eval S M φ)}

/-- Every model of the premises passes the conclusion predicate. -/
def entails {S : Sign} (accepts : D → Prop) (Γ : Set (E.Sen.obj S))
    (φ : E.Sen.obj S) : Prop :=
  ∀ M ∈ E.modelsOf accepts Γ, accepts (E.eval S M φ)

end Evaluation

/-- Change of signature commutes with evaluation in a single fixed value sort. -/
structure ExactInstitution (Sign : Type u) [Category.{v} Sign] (D : Type d)
    extends Evaluation.{u,v,w,m₁,m₂,d} Sign D where
  eval_map : ∀ {S T : Sign} (σ : S ⟶ T) (M : Mod.obj (op T)) (φ : Sen.obj S),
    eval T M (Sen.map σ φ) = eval S ((Mod.map σ.op).toFunctor.obj M) φ

namespace ExactInstitution

variable (I : ExactInstitution.{u,v,w,m₁,m₂,d} Sign D)

/-- Observe any predicate of the evaluation. Equality preserves it in both directions. -/
def observe (accepts : D → Prop) : ClassicInstitution.{u,v,w,m₁,m₂} Sign where
  Sen := I.Sen
  Mod := I.Mod
  Sat S M φ := accepts (I.eval S M φ)
  satisfaction σ M φ := Iff.of_eq (congrArg accepts (I.eval_map σ M φ))

/-- The upper cut at a fixed threshold. -/
def cut [LE D] (threshold : D) : ClassicInstitution.{u,v,w,m₁,m₂} Sign :=
  I.observe (threshold ≤ ·)

/-- Read a proposition-valued evaluation as satisfaction. -/
def toClassic (P : ExactInstitution.{u,v,w,m₁,m₂,0} Sign Prop) :
    ClassicInstitution.{u,v,w,m₁,m₂} Sign :=
  P.observe id

/-- Embed ordinary satisfaction using propositional extensionality. -/
def ofClassic (J : ClassicInstitution.{u,v,w,m₁,m₂} Sign) :
    ExactInstitution.{u,v,w,m₁,m₂,0} Sign Prop where
  Sen := J.Sen
  Mod := J.Mod
  eval := J.Sat
  eval_map σ M φ := propext (J.satisfaction σ M φ)

end ExactInstitution

/-- Each fixed type index has its own sentence functor and denotation sort.
Signature translation preserves the index and evaluation lands in exactly its denotation. -/
structure TypedInstitution (Sign : Type u) [Category.{v} Sign]
    {Code : Type c} (Denote : Code → Type d) where
  Sen : Code → Sign ⥤ Type w
  Mod : Signᵒᵖ ⥤ Cat.{m₁, m₂}
  eval : (t : Code) → (S : Sign) → Mod.obj (op S) → (Sen t).obj S → Denote t
  eval_map : ∀ (t : Code) {S T : Sign} (σ : S ⟶ T) (M : Mod.obj (op T))
    (φ : (Sen t).obj S),
    eval t T M ((Sen t).map σ φ) = eval t S ((Mod.map σ.op).toFunctor.obj M) φ

namespace TypedInstitution

variable {Code : Type c} {Denote : Code → Type d}

/-- Fix the type of the syntax and the matching value sort. -/
def atType (I : TypedInstitution.{u,v,w,m₁,m₂,d,c} Sign Denote) (t : Code) :
    ExactInstitution.{u,v,w,m₁,m₂,d} Sign (Denote t) where
  Sen := I.Sen t
  Mod := I.Mod
  eval := I.eval t
  eval_map := I.eval_map t

/-- Designate a propositional code by an equivalence with Lean's `Prop` and
read its evaluation as ordinary satisfaction. -/
def propInstitution (I : TypedInstitution.{u,v,w,m₁,m₂,d,c} Sign Denote) (t : Code)
    (truth : Denote t ≃ Prop) : ClassicInstitution.{u,v,w,m₁,m₂} Sign :=
  (I.atType t).observe truth

end TypedInstitution

/-- Regard a fixed value type as a typed institution with a single type code. -/
def ExactInstitution.toTyped (I : ExactInstitution.{u,v,w,m₁,m₂,d} Sign D) :
    TypedInstitution.{u,v,w,m₁,m₂,d,0} Sign (fun _ : Unit => D) where
  Sen _ := I.Sen
  Mod := I.Mod
  eval _ := I.eval
  eval_map _ := I.eval_map

/-- Order-lax evaluation. A reduct's value lies below the translated sentence's value.
In particular an upper cut transfers from the reduct to the target. -/
structure LaxInstitution (Sign : Type u) [Category.{v} Sign] (D : Type d) [Preorder D]
    extends Evaluation.{u,v,w,m₁,m₂,d} Sign D where
  le_eval_map : ∀ {S T : Sign} (σ : S ⟶ T) (M : Mod.obj (op T)) (φ : Sen.obj S),
    eval S ((Mod.map σ.op).toFunctor.obj M) φ ≤ eval T M (Sen.map σ φ)

namespace ExactInstitution

/-- An exact evaluation satisfies the order-lax law in any preorder on its values. -/
def toLax [Preorder D] (I : ExactInstitution.{u,v,w,m₁,m₂,d} Sign D) :
    LaxInstitution.{u,v,w,m₁,m₂,d} Sign D where
  toEvaluation := I.toEvaluation
  le_eval_map σ M φ := (I.eval_map σ M φ).ge

end ExactInstitution

namespace LaxInstitution

variable [Preorder D] (I : LaxInstitution.{u,v,w,m₁,m₂,d} Sign D)

/-- The target passes the cut only if the reduct passes it. With laxity this
is exactly the extra condition for the cut to give ordinary satisfaction. -/
def ReflectsCut (threshold : D) : Prop :=
  ∀ {S T : Sign} (σ : S ⟶ T) (M : I.Mod.obj (op T)) (φ : I.Sen.obj S),
    threshold ≤ I.eval T M (I.Sen.map σ φ) →
      threshold ≤ I.eval S ((I.Mod.map σ.op).toFunctor.obj M) φ

/-- An upper cut is an ordinary institution when it also reflects along all signature maps. -/
def cut (threshold : D) (reflects : I.ReflectsCut threshold) :
    ClassicInstitution.{u,v,w,m₁,m₂} Sign where
  Sen := I.Sen
  Mod := I.Mod
  Sat S M φ := threshold ≤ I.eval S M φ
  satisfaction σ M φ := ⟨reflects σ M φ, fun h => h.trans (I.le_eval_map σ M φ)⟩

end LaxInstitution

/-- Independent positive and negative evidence flags. Their interpretation is
supplied by the construction that produces them. -/
@[ext] structure Evidence where
  positive : Prop
  negative : Prop

namespace Evidence

/-- Information order: either flag can be added independently. -/
instance : PartialOrder Evidence where
  le a b := (a.positive → b.positive) ∧ (a.negative → b.negative)
  le_refl _ := ⟨id, id⟩
  le_trans _ _ _ hab hbc := ⟨hbc.1 ∘ hab.1, hbc.2 ∘ hab.2⟩
  le_antisymm _ _ hab hba := Evidence.ext (propext ⟨hab.1, hba.1⟩) (propext ⟨hab.2, hba.2⟩)

/-- Embed true, false and unknown as the three cases without conflicting evidence. -/
def ofThree (value : Option Bool) : Evidence :=
  ⟨value = some true, value = some false⟩

/-- Universal satisfaction and universal refutation over a family of completions. -/
def ofCompletions {M : Type*} (completions : Set M) (holds : M → Prop) : Evidence :=
  ⟨∀ x ∈ completions, holds x, ∀ x ∈ completions, ¬ holds x⟩

end Evidence

namespace Evaluation

variable (E : Evaluation.{u,v,w,m₁,m₂,d} Sign D)

/-- Classify an observed conclusion over the models of the observed premises.
The negative flag requires that every such model fails the conclusion predicate. -/
def entailmentEvidence {S : Sign} (accepts : D → Prop) (Γ : Set (E.Sen.obj S))
    (φ : E.Sen.obj S) : Evidence :=
  Evidence.ofCompletions (E.modelsOf accepts Γ) (fun M => accepts (E.eval S M φ))

end Evaluation

end Silmaril.Logic.Institution.Generalized
