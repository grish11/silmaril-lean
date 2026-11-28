module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Defs

/-! # Reindexing guarded stateful observations and scripts -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

universe u v w

variable {labels : Nat} {α : Type u} {σ : Type v} {τ : Type w}

def Outcome.mapState (f : σ → τ) : Outcome labels α σ → Outcome labels α τ
  | .ret i a s => .ret i a (f s)
  | .fault s => .fault (f s)
  | .diverge => .diverge

/-- Map only the store in ordinary outcomes. Fresh UB remains fresh top. -/
def Behaviour.mapState (f : σ → τ) (b : Behaviour labels α σ) : Behaviour labels α τ :=
  b.map (Set.image (Outcome.mapState f))

namespace Shape.Category.FiniteIteration

variable {n m results : Nat}

def Result.mapState (f : Fin n → Fin m) : Result results n → Result results m
  | .ret i s => .ret i (f s)
  | .fault s => .fault (f s)
  | .diverge => .diverge
  | .ub => .ub

abbrev Syntax.Reply.mapState {A : Syntax.Ty} (f : Fin n → Fin m) :
    Syntax.Reply A n → Syntax.Reply A m := Syntax.StateReply.mapState f

end Shape.Category.FiniteIteration

namespace Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {R : List Syntax.Ty} {n m : Nat}

def StateTransition.mapState (f : σ → τ) : StateTransition R σ → StateTransition R τ
  | .exit i selected s => .exit i selected (f s)
  | .repeat p s => .repeat p (f s)
  | .fault s => .fault (f s)
  | .diverge => .diverge

abbrev Transition.mapState (f : Fin n → Fin m) : Transition R n → Transition R m :=
  StateTransition.mapState f

namespace InterpreterScript

def Query.mapState (f : Fin n → Fin m) (q : Query Φ n) : Query Φ m :=
  ⟨q.op, q.arg, f q.state⟩

/-- Transport both the incoming key state and each successful or fault
answer state. The opcode and typed argument and reply payloads are fixed. -/
def Row.mapState (f : Fin n → Fin m) (row : Row Φ n) : Row Φ m :=
  ⟨row.1.mapState f, row.2.mapState f⟩

end InterpreterScript
end Shape.DependentRequestTree.NativeExtraction.OpenOperands
end Silmaril.Isotope.LambdaSSA.UB.Overlay
