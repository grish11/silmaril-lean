module

public import Silmaril.Logic.Institution.Basic
public import Silmaril.Raw.SSA.Isotope.Institution.InstrSig
public import Silmaril.Raw.SSA.Isotope.Semantics.Relation
public import Silmaril.Raw.SSA.Isotope.Theory.Contexts

/-! # Shared relational models and indexed equations for the Isotope institutions -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Relational

open CategoryTheory Semantics

universe u v i p q

variable {τ ε : Type u} {P Q : InstrSig τ ε} {D : τ → Type v}

/-- A model interprets each native instruction by a typed relation on the fixed value family. -/
abbrev Model (D : τ → Type v) (P : InstrSig τ ε) := RelationModel D P.Instr

namespace Model

/-- A model arrow includes the successful outcomes of every primitive call. -/
def Refines (M N : Model D P) : Prop :=
  ∀ (f : P.Instr) (a : D (instrSrc f)) (b : D (instrTrg f)), M.eval f a b → N.eval f a b

instance : Category (Model D P) where
  Hom M N := PLift (Refines M N)
  id _ := ⟨fun _ _ _ h => h⟩
  comp f g := ⟨fun op a b h => g.down op a b (f.down op a b h)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance (M N : Model D P) : Subsingleton (M ⟶ N) :=
  inferInstanceAs (Subsingleton (PLift (Refines M N)))

/-- Restrict the primitive interpretation along the label map, using its type equalities. -/
def reduct (g : P ⟶ Q) (M : Model D Q) : Model D P :=
  ⟨fun f a b => M.eval (g.instr f)
    (cast (congrArg D (g.source f).symm) a)
    (cast (congrArg D (g.target f).symm) b)⟩

/-- Restrict primitive inclusions along the same label map. -/
def reductFunctor (D : τ → Type v) (g : P ⟶ Q) : Model D Q ⥤ Model D P where
  obj := reduct g
  map h := ⟨fun f _ _ k => h.down (g.instr f) _ _ k⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end Model

/-- Two typed endpoints at a common judgment index. -/
structure Equation {I : Type i} (Program : I → Type p) where
  index : I
  lhs : Program index
  rhs : Program index

/-- Apply an index-preserving program map to both endpoints. -/
def Equation.map {I : Type i} {F : I → Type p} {G : I → Type q}
    (f : ∀ j, F j → G j) (e : Equation F) : Equation G :=
  ⟨e.index, f _ e.lhs, f _ e.rhs⟩

end Silmaril.Isotope.Institution.Relational
