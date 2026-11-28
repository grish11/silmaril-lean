module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Thms

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open CategoryTheory LocallyNameless Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

namespace Program

/-- The written injection of the native input into the left sum arm. -/
def inl (A B : τ) : Program Φ A (coprod A B) := ⟨.inl (.bv 0), .inl .bv⟩

/-- The written injection of the native input into the right sum arm. -/
def inr (A B : τ) : Program Φ B (coprod A B) := ⟨.inr (.bv 0), .inr .bv⟩

/-- Case on the input and give only the selected payload to its arm. -/
def desc {A B C : τ} (left : Program Φ A C) (right : Program Φ B C) :
    Program Φ (coprod A B) C :=
  ⟨.case (.bv 0) left.1.underBinder right.1.underBinder,
    .case .bv left.2.underBinder right.2.underBinder⟩

/-- Eliminate a value in the sole empty-typed input slot. -/
def abort (C : τ) : Program Φ (empty : τ) C := ⟨.abort (.bv 0), .abort .bv⟩

end Program

namespace Interface

/-- The native sum type at the fixed interpretation and policy. -/
def sum (A B : Interface M policy) : Interface M policy := ⟨coprod A.ty B.ty⟩

/-- The native empty type at the fixed interpretation and policy. -/
def zero : Interface M policy := ⟨empty⟩

end Interface

namespace Arrow

def inl (A B : Interface M policy) : A ⟶ A.sum B :=
  ofProgram (Program.inl A.ty B.ty)

def inr (A B : Interface M policy) : B ⟶ A.sum B :=
  ofProgram (Program.inr A.ty B.ty)

def abort (C : Interface M policy) : Interface.zero ⟶ C :=
  ofProgram (Program.abort C.ty)

end Arrow
end Silmaril.Isotope.LetCase.HandledTrace
