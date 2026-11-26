module

public import Silmaril.Logic.ITree.Institution.Thms
public import Silmaril.Semantics.ITree.Signature.Trace.Thms

/-! # An institution of finite handled-trace predicates -/

@[expose] public section

namespace Silmaril.Logic.ITree.TraceInstitution

open CategoryTheory Silmaril.Elgot.ITree

universe u v w

variable {S T : TraceSignature.{u}}

/-- A predicate may inspect the whole finite observation, including the pending
request or prefix following any completed exchanges. -/
structure Sentence (S : TraceSignature.{u}) where
  Result : Type v
  program : Tree S.toSignature.Event Result
  accepts : Trace S.toSignature.Event Result → Prop

/-- Translate the tree and take the direct image of the predicate. Observations
outside the trace map's image are rejected. -/
noncomputable def Sentence.translate (f : S ⟶ T) (φ : Sentence.{u,v} S) : Sentence.{u,v} T :=
  ⟨φ.Result, f.hom.tree id φ.program, fun p' => ∃ p, φ.accepts p ∧ f.trace p = p'⟩

/-- Translate the predicate along every reply lift. A target trace is
accepted when it projects to an accepted source trace. -/
def Sentence.translateLift (f : S.toSignature ⟶ T.toSignature) (φ : Sentence.{u,v} S) : Sentence.{u,v} T :=
  ⟨φ.Result, f.tree id φ.program, fun q => ∃ p, φ.accepts p ∧ f.TraceLift p q⟩

/-- Every finite observation admitted by the handler from this state is accepted. -/
def SatAt (M : Model.{u,w} S.toSignature) (φ : Sentence.{u,v} S) (x : M.State) : Prop :=
  ∀ p, HandledTrace M.step x φ.program p → φ.accepts p

/-- Satisfaction requires the trace predicate from every initial state. -/
def Sat (M : Model.{u,w} S.toSignature) (φ : Sentence.{u,v} S) : Prop :=
  ∀ x, M.initial x → SatAt M φ x

end Silmaril.Logic.ITree.TraceInstitution
