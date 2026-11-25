module

public import Silmaril.SSA.Thesis.SyntacticCategory.Values.Thms

/-! # Tensoring a syntactic computation with a fixed left argument -/

@[expose] public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open scoped MonoidalCategory
open LocallyNameless

variable {S : Sig.{u}}

/-- Run a one-variable term on the newest variable of an ambient context. -/
def onNewest {n : Nat} (t : Tm Empty S.Instr 1) : Tm Empty S.Instr (n + 1) :=
  Tm.rename (fun _ => 0) t

/-- Redirect a one-variable term to the newest variable of the same type. -/
def onNewestTyping {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty} {t : Tm Empty S.Instr 1}
    (h : HasType S.Instr Ctx.nil (.snoc .nil A) t B) :
    HasType S.Instr Ctx.nil (.snoc β A) (onNewest t) B :=
  h.rename ⟨fun _ => 0, Fin.cases rfl (fun i => i.elim0)⟩

/-- Apply a computation to the right slot and pair its result with the left slot. -/
def tensorLeftBody {n : Nat} (t : Tm Empty S.Instr 1) : Tm Empty S.Instr (n + 2) :=
  .let₁ (onNewest t) (.pair (.bv 2) (.bv 0))

/-- Typing of the computation in the two unpacked slots. -/
def tensorLeftBodyTyping {n : Nat} {β : BoundCtx S.Ty n} {R A B : S.Ty}
    {t : Tm Empty S.Instr 1} (h : HasType S.Instr Ctx.nil (.snoc .nil A) t B) :
    HasType S.Instr Ctx.nil (.snoc (.snoc β R) A) (tensorLeftBody t) (tensor R B) :=
  .let₁ (onNewestTyping h) (.pair (.bv (ι := 2)) HasType.newest)

/-- Open the input pair before evaluating its right component. -/
def tensorLeftTm (t : Tm Empty S.Instr 1) : Tm Empty S.Instr 1 :=
  .let₂ (.bv 0) (tensorLeftBody t)

/-- Typing of the one-variable tensor of a computation. -/
def tensorLeftTyping {R A B : S.Ty} {t : Tm Empty S.Instr 1}
    (h : HasType S.Instr Ctx.nil (.snoc .nil A) t B) :
    HasType S.Instr Ctx.nil (.snoc .nil (tensor R A)) (tensorLeftTm t) (tensor R B) :=
  .let₂ (A := R) (B := A) HasType.newest (tensorLeftBodyTyping h)

/-- Retain the left product component while computing on the right one. -/
def tensorLeft (R : SynCat S) {A B : SynCat S} (f : A ⟶ B) :
    productObj R A ⟶ productObj R B :=
  Quotient.map
    (fun a => ⟨tensorLeftTm a.1, a.2.map (tensorLeftTyping (R := R.ty))⟩)
    (fun _ _ h => Eqv.let₂ (Eqv.refl (HasType.newest (A := tensor R.ty A.ty)))
      (Eqv.let₁ (Eqv.rename ⟨fun _ => 0, Fin.cases rfl (fun i => i.elim0)⟩ h)
        (Eqv.refl (.pair (.bv (ι := 2)) HasType.newest)))) f

/-- On any typed representative, left tensoring is destructuring followed by one let. -/
theorem tensorLeft_mk (R : SynCat S) {A B : SynCat S} {t : Tm Empty S.Instr 1}
    (h : HasType S.Instr Ctx.nil (.snoc .nil A.ty) t B.ty) :
    tensorLeft R (A := A) (B := B) (mk h) = mk (tensorLeftTyping (R := R.ty) h) := rfl

/-- The swap isomorphism in the syntactic value category. -/
def valueSwap (A B : SynCat S) :
    (⟨productObj A B⟩ : ValueCat S) ≅ ⟨productObj B A⟩ :=
  letI : BraidedCategory (ValueCat S) := BraidedCategory.ofCartesianMonoidalCategory
  BraidedCategory.braiding (⟨A⟩ : ValueCat S) ⟨B⟩

/-- The computation image of the pure swap. -/
def tensorSwap (A B : SynCat S) : productObj A B ≅ productObj B A :=
  (values S).mapIso (valueSwap A B)

/-- Compute on the first component and retain the second, using pure swaps. -/
def tensorRight (R : SynCat S) {A B : SynCat S} (f : A ⟶ B) :
    productObj A R ⟶ productObj B R :=
  (tensorSwap A R).hom ≫ tensorLeft R f ≫ (tensorSwap B R).inv

/-- The tensor unit of the syntactic computation category is the syntax unit type. -/
def tensorUnit (S : Sig.{u}) : SynCat S :=
  of (unit : S.Ty)

/-- The pure Cartesian left unitor viewed in the computation category. -/
def tensorLeftUnitor (A : SynCat S) : productObj (tensorUnit S) A ≅ A :=
  (values S).mapIso (MonoidalCategoryStruct.leftUnitor (⟨A⟩ : ValueCat S))

/-- The pure Cartesian right unitor viewed in the computation category. -/
def tensorRightUnitor (A : SynCat S) : productObj A (tensorUnit S) ≅ A :=
  (values S).mapIso (MonoidalCategoryStruct.rightUnitor (⟨A⟩ : ValueCat S))

end Silmaril.Thesis.LambdaIter.Syn.SynCat
