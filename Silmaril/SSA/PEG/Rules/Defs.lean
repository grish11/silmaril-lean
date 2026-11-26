module

public import Silmaril.SSA.PEG.Semantics.Thms
public import Silmaril.SSA.PEG.Thms

/-! # Invariance and typed rewrite premises for guarded PEGs -/

@[expose] public section

namespace Silmaril.SSA.PEG.Rules

open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results ins : List (Ty Data)} {out : Ty Data} {n l : Nat}
variable {g : Graph P params results n l} {m : Interpretation.{u,v,x} P}

/-- The two iteration vectors agree outside the designated loop coordinate. -/
def AgreeExcept (loop : Fin l) (i j : Index l) : Prop :=
  ∀ k, k ≠ loop → i k = j k

/-- Definition 5.2 propagates through all edges except sampling at the same loop.
This excludes eval's source and pass's predicate, and includes eval's count. -/
def InvarianceEdge (g : Graph P params results n l) (loop : Fin l)
    (a : Fin n) (kind : EdgeKind (Fin l)) (b : Fin n) : Prop :=
  g.Edge a kind b ∧ kind ≠ .sample loop

/-- The walk presentation of Definition 5.2. No propagated dependency, including
this vertex itself, can be a theta at the designated loop. -/
def InvariantAt (g : Graph P params results n l) (loop : Fin l) (a : Fin n) : Prop :=
  ∀ b ks, Walk (InvarianceEdge g loop) a ks b → (g.node b).label.thetaLoop ≠ some loop

/-- Read a typed reference in an actual or proposed Figure 11 valuation. -/
def readRef (values : g.Valuation m) (r : Ref g.sort out) (i : Index l) : Option (m.Value out) :=
  r.read m.carrier (values (r.id, i))

/-- Bottom is included in both invariance and stream equality. -/
def Invariant (values : g.Valuation m) (loop : Fin l) (r : Ref g.sort out) : Prop :=
  ∀ i j, AgreeExcept loop i j → readRef values r i = readRef values r j

def StreamEq (values : g.Valuation m) (a b : Ref g.sort out) : Prop :=
  ∀ i, readRef values a i = readRef values b i

/-- The typed label and the entire ordered operand tuple of the named row. -/
def HasNode (r : Ref g.sort out) (label : Label P params (Fin l) ins out)
    (args : Tuple (Ref g.sort) ins) : Prop :=
  HEq (g.node r.id) (Node.ofLabel label args)

end Silmaril.SSA.PEG.Rules
