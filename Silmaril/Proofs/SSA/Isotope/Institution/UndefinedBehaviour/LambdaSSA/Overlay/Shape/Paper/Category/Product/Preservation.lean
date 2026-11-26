module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Product.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Product.Whisker
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Representatives
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Product
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.ValueRules

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product

open Silmaril Isotope LambdaSSA CategoryTheory
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape (ValueTyped)
open LambdaSSA.UB.Overlay.Shape.Paper (singletonInterpretation singletonInterpretation_map_ofRegion)
open LambdaSSA.UB.Overlay.Shape.Category (singlePayload splitPair pairPayload valueArrow arrow_ext repackage)
open LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion exists_ofRegion ofRegion_eq_iff pairArrows diagonalArrow
  whiskerLeft_ofRegion whiskerRight_ofRegion)
open LambdaSSA.Region.CfgEta.TypeCategory (whiskerLeftRegion_typed whiskerRightRegion_typed productFstBranches
  productSndBranches returnRegion_branchValue)
open LambdaSSA.Region (ValueBranches)
open LambdaSSA.Semantics (extend)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category (ops outcomes_of_regionAt branch_outcomes)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation (PureValue branchValue_pure_typed)
open Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent (let₂_pure)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {A B C X : Ty κ}
variable (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))

local notation "F" => singletonInterpretation M
local notation "Payload" => singlePayload (atomType := M.atomType)

theorem map_whiskerLeft (X : Ty κ) (f : ofType (Φ := Φ) A ⟶ ofType B) :
    (F).map (Region.Paper.TypeCategory.whiskerLeft (ofType X) f) = Shape.Category.whiskerLeft X ((F).map f) := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion f
  rw [whiskerLeft_ofRegion]
  apply arrow_ext
  intro i p s
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  obtain ⟨_, typed⟩ := p
  cases typed with
  | @pair l a _ _ hl ha =>
    exact (singletonInterpretation_map_ofRegion M (whiskerLeftRegion_typed X hr) (.pair hl ha) s).trans
      ((left_outcomes M.raw l a hr s).trans
        (congrArg (fun b => repackage b (.pair l)) (singletonInterpretation_map_ofRegion M hr ha s).symm))

theorem map_whiskerRight (f : ofType (Φ := Φ) A ⟶ ofType B) (X : Ty κ) :
    (F).map (Region.Paper.TypeCategory.whiskerRight f (ofType X)) = Shape.Category.whiskerRight ((F).map f) X := by
  obtain ⟨r, hr, rfl⟩ := exists_ofRegion f
  rw [whiskerRight_ofRegion]
  apply arrow_ext
  intro i p s
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  obtain ⟨_, typed⟩ := p
  cases typed with
  | @pair a rv _ _ ha hrv =>
    exact (singletonInterpretation_map_ofRegion M (whiskerRightRegion_typed X hr) (.pair ha hrv) s).trans
      ((right_outcomes M.raw a rv hr s).trans
        (congrArg (fun beh => repackage beh (fun b => .pair b rv)) (singletonInterpretation_map_ofRegion M hr ha s).symm))

private theorem unpack_branch {t : Tm Φ} (l r b : Value M.raw.α)
    (ht : t.HasType [B, A, .product A B] C)
    (pure : PureValue (ops M.raw) (extend (extend (extend (envOfBound M.raw.bound) (.pair l r)) l) r) t b)
    (s : M.raw.σ) :
    nativeOutcomes (⟨.let₂ (.var 0) (.br 0 t), .let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl ht)⟩ :
      UB.Typed (Φ := Φ) [.product A B] [C]) (extendModel M.raw (.pair l r)) s =
      {Outcome.ret 0 b s} := by
  let P := extendModel M.raw (.pair l r)
  let Q := extendModel (extendModel P l) r
  have hP := (envOfBound_agrees M.raw.bound).extend (.pair l r)
  have hQ := (hP.extend l).extend r
  exact (outcomes_of_regionAt M.raw _ ⟨.br 0 t, .br (ℓ := 0) rfl ht⟩ hP hQ
    (let₂_pure (PureValue.var 0) (.br 0 t)) s).trans (branch_outcomes Q hQ ht pure s)

theorem map_productFst (A B : Ty κ) :
    (F).map (ofRegion (productFstBranches (Φ := Φ) A B)) =
      valueArrow (fun p : Payload (.product A B) => (splitPair p).1) := by
  apply arrow_ext
  intro i p s
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  obtain ⟨_, typed⟩ := p
  cases typed with
  | @pair l r _ _ hl hr =>
    exact (singletonInterpretation_map_ofRegion M (productFstBranches A B) (.pair hl hr) s).trans
      (congrArg WithTop.some (unpack_branch M l r l (.var (i := 1) rfl) (PureValue.var 1) s))

theorem map_productSnd (A B : Ty κ) :
    (F).map (ofRegion (productSndBranches (Φ := Φ) A B)) =
      valueArrow (fun p : Payload (.product A B) => (splitPair p).2) := by
  apply arrow_ext
  intro i p s
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  obtain ⟨_, typed⟩ := p
  cases typed with
  | @pair l r _ _ hl hr =>
    exact (singletonInterpretation_map_ofRegion M (productSndBranches A B) (.pair hl hr) s).trans
      (congrArg WithTop.some (unpack_branch M l r r (.var (i := 0) rfl) (PureValue.var 0) s))

private theorem map_branch {t : Tm Φ} (ht : t.BranchValue [A] B)
    (f : Payload A → Payload B)
    (pure : ∀ a : Payload A, PureValue (ops M.raw) (extend (envOfBound M.raw.bound) a.val) t (f a).val) :
    (F).map (ofRegion (.br (ℓ := 0) rfl ht)) = valueArrow f := by
  apply arrow_ext
  intro i a s
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  exact (singletonInterpretation_map_ofRegion M (.br (ℓ := 0) rfl ht) a.property s).trans
    (congrArg WithTop.some (branch_outcomes (extendModel M.raw a.val)
      ((envOfBound_agrees M.raw.bound).extend a.val) ht.hasType (pure a) s))

theorem map_returnTerm_branchValue {t : Tm Φ} (ht : t.BranchValue [A] B) :
    ∃ f : Payload A → Payload B, (F).map (Region.Paper.TypeCategory.returnTerm ht.hasType) = valueArrow f := by
  have eq : Region.Paper.TypeCategory.returnTerm ht.hasType = ofRegion (.br (ℓ := 0) rfl ht) :=
    (ofRegion_eq_iff _ _).mpr (.cfgEta (.native (.base (returnRegion_branchValue ht))))
  rw [eq]
  have pure (a : Payload A) : ∃ b, PureValue (ops M.raw) (extend (envOfBound M.raw.bound) a.val) t b ∧
      ValueTyped M.atomType b B :=
    branchValue_pure_typed ht ((Shape.env_typed M).extend a.property)
  exact ⟨fun a => ⟨(pure a).choose, (pure a).choose_spec.2⟩, map_branch M ht _ (fun a => (pure a).choose_spec.1)⟩

theorem map_diagonal (X : Ty κ) :
    (F).map (diagonalArrow (Φ := Φ) X) = valueArrow (fun x : Payload X => pairPayload x x) :=
  map_branch M (.pair (.var (i := 0) rfl) (.var (i := 0) rfl)) _ (fun _ => (PureValue.var 0).pair (PureValue.var 0))

set_option backward.isDefEq.respectTransparency false in
theorem map_pairArrows_value (f : ofType (Φ := Φ) X ⟶ ofType A) (g : ofType X ⟶ ofType B)
    (a : Payload X → Payload A) (b : Payload X → Payload B)
    (hf : (F).map f = valueArrow a) (hg : (F).map g = valueArrow b) :
    (F).map (pairArrows f g) = valueArrow (fun x => pairPayload (a x) (b x)) := by
  simp only [pairArrows, Functor.map_comp, map_diagonal, map_whiskerRight, map_whiskerLeft, hf, hg,
    Shape.Category.whiskerLeft_value, Shape.Category.whiskerRight_value, Shape.Category.value_comp]
  congr 1

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product
