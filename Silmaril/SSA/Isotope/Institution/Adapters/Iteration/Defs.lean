module

public import Silmaril.SSA.Isotope.Institution.Parallel.Inclusions.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.LetIter.Thms
public import Silmaril.SSA.Isotope.LetParIter.Institution.Restrictions.Thms

/-! # Exact syntax and semantic restrictions from LetParIter -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.Iteration

open CategoryTheory Semantics
open LetIter.ProofRelevant.Semantics (TypeModel TyDen CtxDen BoundDen)
open Parallel.Institution (Equation)

universe u v

variable {τ ε : Type u} [TypeFormers τ] {S T : InstrSig τ ε}
  {ν : Type u} [DecidableEq ν] {Γ : Ctx ν τ}

def ofLetParCase (φ : Equation S .case Γ) : LetParIter.Institution.Sentence S ν :=
  ⟨Γ, φ.n, φ.bound, φ.result, .ofLetParCase φ.lhs, .ofLetParCase φ.rhs⟩

def ofLetIter (φ : Relational.LetIter.Sentence S Γ) : LetParIter.Institution.Sentence S ν :=
  ⟨Γ, φ.1.depth, φ.1.bound, φ.1.result, .ofLetIter φ.2.1.2, .ofLetIter φ.2.2.2⟩

variable [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]

/-- The lower case evaluator uses the upper value model's product, unit, sums, and empty type. -/
@[instance_reducible] def nativeCoproductModel : CoproductModel (TyDen (τ := τ)) :=
  ⟨TypeModel.coprodEquiv⟩

@[instance_reducible] def nativeEmptyModel : EmptyModel (TyDen (τ := τ)) :=
  ⟨(LetParIter.Institution.caseControl τ Id).zero LetParCase.hasCase⟩

attribute [local instance] LetParIter.nativeProductModel LetParIter.nativeUnitModel
  nativeCoproductModel nativeEmptyModel

/-- View the upper environment through visible free-name lookup. -/
def visibleEnv (γ : CtxDen Γ) : FreeEnv (TyDen (τ := τ)) Γ :=
  fun x _ h => CtxDen.lookup γ x h

/-- Rebuild the upper bound environment from every bound variable's value. -/
def nativeBound : {n : Nat} → {β : BoundCtx τ n} →
    BoundEnv (TyDen (τ := τ)) β → BoundDen β
  | _, .nil, _ => PUnit.unit
  | _, .snoc _ _, ρ => (nativeBound (fun i => ρ i.succ), ρ 0)

/-- Forget iteration and retain the upper model's monad, pairing and instruction computations. -/
abbrev caseModel (M : LetParIter.Institution.Model.{u, v} S) :
    Parallel.Institution.Model (TyDen (τ := τ)) S where
  M := M.Carrier
  monad := M.monad
  lawful := M.lawfulMonad
  par x y := M.pairing.pair x y
  instr := ⟨M.instructions.denote⟩

/-- Retain the strict computation map while forgetting its extra upper-tier laws. -/
def caseModelFunctor :
    LetParIter.Institution.Model.{u, v} S ⥤ Parallel.Institution.Model (TyDen (τ := τ)) S where
  obj := caseModel
  map f := ⟨@f.app, Cslib.IsMonadHom.mk' f.map_pure f.map_bind, f.map_pair, f.map_instr⟩
  map_id _ := Parallel.Institution.Model.Hom.ext rfl
  map_comp _ _ := Parallel.Institution.Model.Hom.ext rfl

/-- Sequential equations on the upper models, evaluated by the native LetIter interpreter.
The model category retains lawful Elgot iteration and the upper pure-instruction coherence. -/
def IterSat (M : LetParIter.Institution.Model.{u, v} S) (φ : Relational.LetIter.Sentence S Γ) :
    Prop :=
  ∀ (γ : CtxDen Γ) (ρ : BoundDen φ.1.bound),
    M.evalLetIter φ.2.1.2 γ ρ = M.evalLetIter φ.2.2.2 γ ρ

/-- A native upper model at the existing finite-success powerset Elgot iteration.
The instruction model includes the native bottom-effect coherence law. -/
abbrev setModel (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (I : LetIter.ProofRelevant.Semantics.InstructionModel S.Instr τ ε SetM) :
    LetParIter.Institution.Model.{u, v} S where
  Carrier := SetM
  pairing := pair
  instructions := I

/-- The primitive successful-result relation of the fixed native powerset model. -/
def setRelations (I : LetIter.ProofRelevant.Semantics.InstructionModel S.Instr τ ε SetM) :
    Relational.Model (TyDen (τ := τ)) S :=
  RelationModel.ofSetModel ⟨I.denote⟩

end Silmaril.Isotope.Institution.Adapters.Iteration
