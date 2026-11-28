module

public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Defs

/-! # Models and boundaries for the ordered loop translation -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta

open Isotope.LetIter.ProofRelevant.Semantics
open OrderedRuntime.Structured

universe u

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m]
variable {A : τ}

abbrev ValueTuple (A : τ) := Tuple (Values (TyDen (τ := τ))) (carried A)
abbrev ResultTuple (A : τ) := Tuple (Values (TyDen (τ := τ))) (results A)

def pack (a : TyDen A) : ValueTuple A := .cons a .nil

def unpack (a : ValueTuple A) : TyDen A := a.get .head

/-- Zero is the outward branch and one is the local back edge. The two
alternatives carry their own values without duplicating the computation. -/
def packChoice (c : TyDen A ⊕ TyDen A) : ResultTuple A :=
  match c with
  | .inl a => .cons ⟨0⟩ (pack a)
  | .inr a => .cons ⟨1⟩ (pack a)

abbrev Steps (Φ : Type u) [HasTy Φ τ] (m : Type u → Type u) :=
  {A : τ} → Step Φ A → TyDen A → m (TyDen A ⊕ TyDen A)

/-- Interpret the ordered instruction at a pure value boundary. Its result
tag is assembled only after the primitive computation has finished. -/
def orderedModel (f : Steps (τ := τ) Φ m) : OrderedRuntime.Structured.Model (PureOp τ) (EffectOp Φ) m where
  value := TyDen
  runPure op := op.elim
  effect
    | .step s, .cons a .nil => packChoice <$> f s a

/-- Apply a typed ΛSSA primitive and expose its sum via the type model. -/
def stepMap {ε : Type u} [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε m]
    (s : Step Φ A) (a : TyDen A) : m (TyDen A ⊕ TyDen A) := do
  let y ← InstructionModel.denote (ε := ε) (m := m) s.op (s.input.symm ▸ a)
  pure (TypeModel.coprodEquiv A A (s.output ▸ y))

def exit (a : TyDen A) : Isotope.LambdaSSA.Semantics.Monadic.LabelDen [A] := Sum.inl a

/-- The singleton CFG's local label comes before its external exit. -/
def bodyTarget : TyDen A ⊕ TyDen A → Isotope.LambdaSSA.Semantics.Monadic.LabelDen [A,A]
  | .inl a => .inr (exit a)
  | .inr a => .inl a

def exitValue : Isotope.LambdaSSA.Semantics.Monadic.LabelDen [A] → TyDen A
  | .inl a => a
  | .inr bad => nomatch bad

/-- Observe the returned payload and runtime of the ordered θ interpreter. -/
def observe {σ : Type u}
    (res : Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried A))) : TyDen A × σ :=
  let (payload, state) := encode res
  (unpack payload, state)

def point {σ : Type u} (a : TyDen A) (state : σ) :
    Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried A)) :=
  .cons a (.cons state .nil)

/-- Lift a total ordered primitive into partial state computations. Partiality
in this specialization therefore comes from the loop. -/
def liftState {σ : Type u} (f : Steps (τ := τ) Φ (StateM σ)) :
    Steps (τ := τ) Φ (StateT σ Part) :=
  fun s a => StateT.mk fun state => Part.some ((f s a).run state)


/-- Read the numbered loop at the LambdaSSA exit boundary, retaining its final
runtime in the state computation. -/
noncomputable def Related.stateDenotation {σ : Type u}
    {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A} (rel : Related A r g)
    (f : Steps (τ := τ) Φ (StateM σ)) :
    Isotope.LambdaSSA.Semantics.Monadic.Env [A] →
      StateT σ Part.{u} (Isotope.LambdaSSA.Semantics.Monadic.LabelDen [A]) :=
  fun env => StateT.mk fun state =>
    (fun output => (exit (observe output).1, (observe output).2)) <$>
      OrderedRuntime.Structured.Theta.denoteTotal.{u,u,u}
        (orderedModel f) g rel.checked (point env.2 state)

end Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta
