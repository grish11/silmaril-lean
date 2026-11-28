module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Product.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Constructors.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Product.Preservation

/-! # Product comparisons for the shaped guarded singleton interpretation -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open CategoryTheory
open LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion whiskerLeft whiskerRight diagonalArrow pairArrows returnTerm)
open LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)
open Shape.Category (singlePayload splitPair pairPayload valueArrow)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {A B X : Ty κ}
variable (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))

local notation "Payload" => singlePayload (atomType := M.atomType)

/-- The active right component runs at the incoming state. Every successful
exit pairs its reply with the fixed left value at the exit's final state. -/
theorem singleton_map_whiskerLeft (X : Ty κ) (f : ofType (Φ := Φ) A ⟶ ofType B) :
    (singletonInterpretation M).map (whiskerLeft (ofType X) f) =
      Shape.Category.whiskerLeft X ((singletonInterpretation M).map f) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product.map_whiskerLeft M X f

/-- The active left component runs at the incoming state and retains the
fixed right value. Both comparisons include faults and may-divergence. -/
theorem singleton_map_whiskerRight (f : ofType (Φ := Φ) A ⟶ ofType B) (X : Ty κ) :
    (singletonInterpretation M).map (whiskerRight f (ofType X)) =
      Shape.Category.whiskerRight ((singletonInterpretation M).map f) X :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product.map_whiskerRight M f X

theorem singleton_map_productFst (A B : Ty κ) :
    (singletonInterpretation M).map (ofRegion (productFstBranches (Φ := Φ) A B)) =
      valueArrow (fun p : Payload (.product A B) => (splitPair p).1) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product.map_productFst M A B

theorem singleton_map_productSnd (A B : Ty κ) :
    (singletonInterpretation M).map (ofRegion (productSndBranches (Φ := Φ) A B)) =
      valueArrow (fun p : Payload (.product A B) => (splitPair p).2) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product.map_productSnd M A B

/-- Constructor returns denote total state-preserving typed maps. -/
theorem singleton_map_returnTerm_branchValue {t : Tm Φ} (ht : t.BranchValue [A] B) :
    ∃ f : Payload A → Payload B, (singletonInterpretation M).map (returnTerm ht.hasType) = valueArrow f :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product.map_returnTerm_branchValue M ht

theorem singleton_map_diagonal (X : Ty κ) :
    (singletonInterpretation M).map (diagonalArrow (Φ := Φ) X) = valueArrow (fun x : Payload X => pairPayload x x) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product.map_diagonal M X

/-- On arrows certified to denote value maps, the installed sequential
pairing is Cartesian pairing of those maps. -/
theorem singleton_map_pairArrows_value (f : ofType (Φ := Φ) X ⟶ ofType A) (g : ofType X ⟶ ofType B)
    (a : Payload X → Payload A) (b : Payload X → Payload B)
    (hf : (singletonInterpretation M).map f = valueArrow a)
    (hg : (singletonInterpretation M).map g = valueArrow b) :
    (singletonInterpretation M).map (pairArrows f g) = valueArrow (fun x => pairPayload (a x) (b x)) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Product.map_pairArrows_value M f g a b hf hg

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
