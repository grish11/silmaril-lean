module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Family.Thms

/-! # Completing a class map to phases of its target

`Padding h` records how a state map `h : X → Z` becomes the phase fold
after unreachable states are added: padding states `pad` with a class
map, and an iso of default Paper from `pad + X` to phases of `Z` under
which the phase fold is `[cls, h]`. It mentions no table and no section.

`tagPadding` builds it for the class map of every tag map into at least
two classes. Each source state `k` gets one phase: the state itself in
the slot of its class `f k`, and padding in the other slots. So there are
as many phases as source states. The source states are taken in the
written order; nothing is assumed about how the classes are arranged.

The last part restates the tag fold on phases of one payload type, which
is the shape of the literal tables.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The phase fold through one more phase that is split as `M + L`. -/
theorem layer_fold {M L P X Z : τ} (n : Nat) (μ : ofType (Φ := Φ) M ⟶ ofType Z)
    (ℓ : ofType (Φ := Φ) L ⟶ ofType Z) (split : IsIso (sumDesc μ ℓ)) (cls : ofType (Φ := Φ) P ⟶ ofType Z)
    (h : ofType (Φ := Φ) X ⟶ ofType Z) (ψ : ofType (Φ := Φ) (Silmaril.coprod P X) ≅ ofType (phaseType Z n))
    (fold : ψ.hom ≫ phaseFold Z n = sumDesc cls h) :
    (sumInterchange M P L X ≪≫ sumBoth (@asIso _ _ _ _ (sumDesc μ ℓ) split) ψ).hom ≫
        sumDesc (𝟙 _) (phaseFold Z n) = sumDesc (sumDesc μ cls) (sumDesc ℓ h) := by
  rw [Iso.trans_hom, Category.assoc, sumBoth_desc, asIso_hom, Category.comp_id, fold, sumInterchange_desc]

/-- A completion of the state map `h` to phases of its target. -/
structure Padding {X Z : τ} (h : ofType (Φ := Φ) X ⟶ ofType Z) where
  /-- One less than the number of phases. -/
  phases : Nat
  /-- The padding states. -/
  pad : τ
  /-- Their classes. -/
  cls : ofType (Φ := Φ) pad ⟶ ofType Z
  iso : ofType (Φ := Φ) (Silmaril.coprod pad X) ≅ ofType (phaseType Z phases)
  fold : iso.hom ≫ phaseFold Z phases = sumDesc cls h

/-- One state `L` that is a summand of `Z`: the padding is its complement. -/
noncomputable def Padding.single {M L Z : τ} (μ : ofType (Φ := Φ) M ⟶ ofType Z) (ℓ : ofType (Φ := Φ) L ⟶ ofType Z)
    (split : IsIso (sumDesc μ ℓ)) : Padding ℓ where
  phases := 0
  pad := M
  cls := μ
  iso := @asIso _ _ _ _ (sumDesc μ ℓ) split
  fold := Category.comp_id _

/-- One more state `L` in front, again a summand of `Z`. Its complement
is added to the padding and the two fill one more phase. -/
noncomputable def Padding.layer {M L X Z : τ} (μ : ofType (Φ := Φ) M ⟶ ofType Z)
    (ℓ : ofType (Φ := Φ) L ⟶ ofType Z) (split : IsIso (sumDesc μ ℓ)) {h : ofType (Φ := Φ) X ⟶ ofType Z}
    (c : Padding h) : Padding (sumDesc ℓ h) where
  phases := c.phases + 1
  pad := Silmaril.coprod M c.pad
  cls := sumDesc μ c.cls
  iso := sumInterchange M c.pad L X ≪≫ sumBoth (@asIso _ _ _ _ (sumDesc μ ℓ) split) c.iso
  fold := layer_fold c.phases μ ℓ split c.cls h c.iso c.fold

variable {m : Nat}

/-- The completion of the class map of any tag map into at least two
classes. -/
noncomputable def tagPadding (A : Fin (m + 2) → τ) :
    (N : Nat) → (f : Fin (N + 1) → Fin (m + 2)) → Padding (tagFold (Φ := Φ) A f)
  | 0, f => Padding.single (famMiss m A (f 0)) (famInj (m + 1) A (f 0)) (famSplit A (f 0))
  | N + 1, f => (tagPadding A N fun k => f k.succ).layer (famMiss m A (f 0)) (famInj (m + 1) A (f 0))
      (famSplit A (f 0))

/-! ## One payload type -/

/-- The sum of a constant family is the phase type. -/
noncomputable def constIso (A : τ) : (K : Nat) →
    (ofType (Φ := Φ) (famSum K fun _ => A) ≅ ofType (phaseType A K))
  | 0 => Iso.refl _
  | K + 1 => sumBoth (Iso.refl _) (constIso A K)

/-- Phase `i` of `K + 1` phases. -/
noncomputable def phaseInj (A : τ) (K : Nat) (i : Fin (K + 1)) :
    ofType (Φ := Φ) A ⟶ ofType (phaseType A K) :=
  famInj K (fun _ => A) i ≫ (constIso A K).hom

/-- The class map between phases of one payload type. -/
noncomputable def classFold (A : τ) {K K' : Nat} (cls : Fin (K + 1) → Fin (K' + 1)) :
    ofType (Φ := Φ) (phaseType A K) ⟶ ofType (phaseType A K') :=
  (constIso A K).inv ≫ tagFold (fun _ => A) cls ≫ (constIso A K').hom

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
