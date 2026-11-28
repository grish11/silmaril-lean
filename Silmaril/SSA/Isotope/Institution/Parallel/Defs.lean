module

public import Silmaril.SSA.Isotope.Institution.Parallel.Relabel.Defs
public import Silmaril.Logic.Institution.Morphism

/-! Observation models for native LetPar and LetParCase, with a fixed value interpretation. -/

@[expose] public section

namespace Silmaril.Isotope.Parallel.Institution

open Silmaril.Isotope.Institution CategoryTheory Semantics

universe u v q

/-- Fix the value-side control data of a lower tier before choosing a computation monad. -/
def lowerControl {tier : Tier} {τ : Type u} [CaseTypes tier τ] {D : τ → Type q}
    (h : tier ≠ .iter) (C : Control tier D Id) (m : Type q → Type q) : Control tier D m where
  sum := C.sum
  zero := C.zero
  loop hi := (h hi).elim

namespace Primitive

variable {τ ε : Type u} {S S' : InstrSig τ ε}
  {D : τ → Type q} {m : Type q → Type q}

/-- Restrict primitive evaluation along a map preserving exact source and target types. -/
def reduct (f : S ⟶ S') (M : InstructionModel D S'.Instr m) :
    InstructionModel D S.Instr m where
  eval op x := f.target op ▸ M.eval (f.instr op) ((f.source op).symm ▸ x)

end Primitive

/-- A lawful monad, its supplied parallel operation, and typed primitive interpretations.
The operation is part of the observation model; equations for it may be tested as sentences. -/
structure Model {τ ε : Type u} (D : τ → Type q) (S : InstrSig τ ε) where
  M : Type q → Type q
  [monad : Monad M]
  [lawful : LawfulMonad M]
  par : ParOp M
  instr : InstructionModel D S.Instr M

attribute [instance] Model.monad Model.lawful

namespace Model

variable {τ ε : Type u} {D : τ → Type q} {S S' : InstrSig τ ε}

/-- Strict arrows act uniformly on computations and preserve the interpreter operations.
All value carriers and their structural equivalences are fixed. -/
structure Hom (X Y : Model D S) where
  app : {A : Type q} → X.M A → Y.M A
  monadHom : Cslib.IsMonadHom X.M Y.M app
  map_par : ∀ {A B : Type q} (a : X.M A) (b : X.M B),
    app (X.par a b) = Y.par (app a) (app b)
  map_instr : ∀ op x, app (X.instr.eval op x) = Y.instr.eval op x

@[ext] theorem Hom.ext {X Y : Model D S} {f g : Hom X Y}
    (h : @f.app = @g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (Model D S) where
  Hom := Hom
  id X := ⟨id, Cslib.IsMonadHom.id X.M, fun _ _ => rfl, fun _ _ => rfl⟩
  comp f g :=
    ⟨fun x => g.app (f.app x), g.monadHom.comp f.monadHom,
      fun a b => by rw [f.map_par, g.map_par],
      fun op x => by rw [f.map_instr, g.map_instr]⟩
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

/-- Restrict the instruction alphabet, retaining both monadic and parallel structure. -/
def reduct (f : S ⟶ S') (X : Model D S') : Model D S :=
  { M := X.M
    monad := X.monad
    lawful := X.lawful
    par := X.par
    instr := Primitive.reduct f X.instr }

private theorem app_cast {F G : Type q → Type q} (app : {A : Type q} → F A → G A)
    {A B : τ} (h : A = B) (x : F (D A)) :
    app (h ▸ x : F (D B)) = (h ▸ app x : G (D B)) := by
  cases h
  rfl

/-- The reduct retains each strict hom's computation map. -/
def reductFunctor (f : S ⟶ S') : Model D S' ⥤ Model D S where
  obj X := X.reduct f
  map h :=
    ⟨@h.app, h.monadHom, h.map_par, fun op x => by
      unfold Model.reduct Primitive.reduct
      dsimp only
      rw [app_cast (@h.app) (f.target op), h.map_instr]⟩
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

end Model

variable {τ ε : Type u} {tier : Tier} {ν : Type v}
  [HasProduct τ] [HasUnit τ] [CaseTypes tier τ] [DecidableEq ν]

/-- An equation between two particular exact derivations in the same contexts and
result type. The sentence retains the chosen typing witnesses for interpretation. -/
structure Equation (S : InstrSig τ ε) (tier : Tier) [CaseTypes tier τ] (Γ : Ctx ν τ) where
  n : Nat
  bound : BoundCtx τ n
  result : τ
  left : Tm tier ν S.Instr n
  right : Tm tier ν S.Instr n
  lhs : Derivation S.Instr Γ bound left result
  rhs : Derivation S.Instr Γ bound right result

namespace Equation

variable {Γ : Ctx ν τ} {S S' : InstrSig τ ε}

/-- Translate each native endpoint and its typing evidence. -/
def map (f : S ⟶ S') (φ : Equation S tier Γ) : Equation S' tier Γ :=
  ⟨φ.n, φ.bound, φ.result, φ.left.mapInstr f.instr, φ.right.mapInstr f.instr,
    φ.lhs.mapInstr f, φ.rhs.mapInstr f⟩

variable {D : τ → Type q} [ProductModel D] [UnitModel D]

/-- Sentence truth means equality of full monadic computations for all environments. -/
def Holds (φ : Equation S tier Γ) (X : Model D S)
    (C : Control tier D X.M) : Prop :=
  ∀ (γ : FreeEnv D Γ) (ρ : BoundEnv D φ.bound),
    φ.lhs.denote D X.instr X.par C γ ρ = φ.rhs.denote D X.instr X.par C γ ρ

end Equation

end Silmaril.Isotope.Parallel.Institution
