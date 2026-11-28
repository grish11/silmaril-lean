module

public import Silmaril.SSA.Isotope.Institution.Parallel.Defs
public import Silmaril.SSA.Isotope.Institution.Parallel.Relabel.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.Parallel.Room

@[expose] public section

namespace Silmaril.Isotope.Parallel.Institution

open Silmaril.Isotope.Institution Silmaril.Logic.Institution CategoryTheory Semantics

universe u v q

variable {τ ε : Type u} {S S' S'' : InstrSig τ ε} {D : τ → Type q}

namespace Model

@[simp] theorem reductFunctor_id (S : InstrSig τ ε) :
    reductFunctor (D := D) (𝟙 S) = 𝟭 (Model D S) :=
  InstitutionProofs.reductFunctor_id S

theorem reductFunctor_comp (f : S ⟶ S') (g : S' ⟶ S'') :
    reductFunctor (D := D) (f ≫ g) = reductFunctor g ⋙ reductFunctor f :=
  InstitutionProofs.reductFunctor_comp f g

end Model

variable {tier : Tier} {ν : Type v} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
  [DecidableEq ν] [ProductModel D] [UnitModel D] {Γ : Ctx ν τ}

theorem denote_mapInstr {n : Nat} {β : BoundCtx τ n} {t : Tm tier ν S.Instr n} {A : τ}
    {m : Type q → Type q} [Monad m] (I : InstructionModel D S'.Instr m)
    (P : ParOp m) (C : Control tier D m) (f : S ⟶ S') (d : Derivation S.Instr Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (d.mapInstr f).denote D I P C γ ρ =
      d.denote D (Primitive.reduct f I) P C γ ρ :=
  InstitutionProofs.denote_mapInstr I P C f d γ ρ

/-- Strict model arrows preserve exact lower-tier interpreter results. -/
theorem denote_hom {n : Nat} {β : BoundCtx τ n} {t : Tm tier ν S.Instr n} {A : τ}
    {X Y : Model D S} (H : Model.Hom X Y) (h : tier ≠ .iter)
    (C : Control tier D Id) (d : Derivation S.Instr Γ β t A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    H.app (d.denote D X.instr X.par (lowerControl h C X.M) γ ρ) =
      d.denote D Y.instr Y.par (lowerControl h C Y.M) γ ρ :=
  InstitutionProofs.denote_hom H h C d γ ρ

namespace Equation

@[simp] theorem map_id (φ : Equation S tier Γ) : φ.map (𝟙 S) = φ :=
  InstitutionProofs.equation_map_id φ

theorem map_comp (f : S ⟶ S') (g : S' ⟶ S'') (φ : Equation S tier Γ) :
    (φ.map f).map g = φ.map (f ≫ g) :=
  InstitutionProofs.equation_map_comp f g φ

theorem holds_map (f : S ⟶ S') (φ : Equation S tier Γ) (X : Model D S')
    (C : Control tier D X.M) :
    (φ.map f).Holds X C ↔ φ.Holds (X.reduct f) C :=
  InstitutionProofs.holds_map f φ X C

end Equation

/-- Observation at a fixed signature, using a fixed value interpretation and lower-tier control. -/
def room (h : tier ≠ .iter) (C : Control tier D Id) (Γ : Ctx ν τ) (S : InstrSig τ ε) :
    Room.{max u v, q + 1, max u (q + 1)} where
  Sen := Equation S tier Γ
  Mod := Cat.of (Model D S)
  Sat X φ := φ.Holds X (lowerControl h C X.M)

/-- A change of opcode names translates sentences forward and models backward. -/
def corridor (h : tier ≠ .iter) (C : Control tier D Id) (Γ : Ctx ν τ) (f : S ⟶ S') :
    room h C Γ S ⟶ room h C Γ S' :=
  ⟨Equation.map f, Model.reductFunctor f, fun X φ => φ.holds_map f X (lowerControl h C X.M)⟩

/-- The lower parallel observation institution as a functor into rooms. -/
def observation (h : tier ≠ .iter) (C : Control tier D Id) (Γ : Ctx ν τ) :
    InstrSig τ ε ⥤ Room.{max u v, q + 1, max u (q + 1)} where
  obj := room h C Γ
  map := corridor h C Γ
  map_id S := Room.hom_ext (funext Equation.map_id) (Model.reductFunctor_id S)
  map_comp f g :=
    Room.hom_ext (funext fun φ => (φ.map_comp f g).symm) (Model.reductFunctor_comp f g)

end Silmaril.Isotope.Parallel.Institution

namespace Silmaril.Isotope

open Institution Parallel CategoryTheory Silmaril.Logic.Institution Semantics

universe u v q

variable {τ ε : Type u} {ν : Type v} [DecidableEq ν] (Γ : Ctx ν τ)
  (D : τ → Type q)

/-- Native LetPar observes exact computations in the sequential-control tier. -/
def LetPar.observation [HasProduct τ] [HasUnit τ] [ProductModel D] [UnitModel D] :
    InstrSig τ ε ⥤ Room.{max u v, q + 1, max u (q + 1)} :=
  Parallel.Institution.observation (by decide) (Control.seq D Id) Γ

/-- Native LetParCase observes exact computations with sums and empty type. -/
def LetParCase.observation [TypeFormers τ] [ProductModel D] [UnitModel D]
    [CoproductModel D] [EmptyModel D] :
    InstrSig τ ε ⥤ Room.{max u v, q + 1, max u (q + 1)} :=
  Parallel.Institution.observation (by decide) (Control.case D Id) Γ

end Silmaril.Isotope
