module

public import Silmaril.Semantics.RuntimeWires.Sliced.Defs
public import Silmaril.Semantics.RuntimeWires.Presented.Thms

@[expose] public section

namespace Silmaril.RuntimeWires.Sliced

open CategoryTheory
open scoped MonoidalCategory

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

variable (E : Diagram.Equations S)

local notation "Obj" => (Diagram.Presented.mk (S := S) (E := E))

/-- Interpret a row by parallel composition in the algebraic presentation. -/
def Row.denote : {A B : List O} → Row S A B → (Obj A ⟶ Obj B)
  | _, _, .empty => 𝟙 _
  | _, _, .wire x r => (𝟙 (Obj [x])) ⊗ₘ Row.denote r
  | _, _, .box e r =>
    Diagram.Presented.ofTerm (A := Obj (S.source e)) (B := Obj (S.target e)) (.gen e) ⊗ₘ
      Row.denote r

/-- Interpret a sheet by reading its rows from top to bottom. -/
def Sheet.denote : {A B : List O} → Sheet S A B → (Obj A ⟶ Obj B)
  | _, _, .empty _ => 𝟙 _
  | _, _, .cons row rest => row.denote E ≫ Sheet.denote rest

end Silmaril.RuntimeWires.Sliced
