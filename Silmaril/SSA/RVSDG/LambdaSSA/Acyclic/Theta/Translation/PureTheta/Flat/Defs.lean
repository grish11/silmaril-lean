module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Defs

/-! # Link a recovered data-only θ body into a flat CFG -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta

open Sequential
open Translation

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A X Z L E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- The mixed loop has one reachable external exit at a homogeneous join. -/
def Loop.fragment (loop : Loop Φ ε A) : Flat.Fragment Φ A A A :=
  Flat.Fragment.bindChooseLoop loop.value loop.decide

/-- Embed the recovered loop at the homogeneous join interface.
The loop only targets the first external label. -/
def Reverse.Fibre.fragment {g : Reverse.Graph Φ ε A} (f : Reverse.Fibre g) :
    Flat.Fragment Φ A A A :=
  f.loop.fragment

/-- The two numbered component certificates determine one flat block table. -/
structure Link (g : Reverse.Graph Φ ε A)
    (layout : Layout τ A X Z L E D sigs) (h : Flat.Serial.Graph Φ A X Z L E D sigs) where
  first : Reverse.Fibre g
  next : Translation.Fibre layout h

def Link.fragment {g : Reverse.Graph Φ ε A} {layout : Layout τ A X Z L E D sigs}
    {h : Flat.Serial.Graph Φ A X Z L E D sigs} (f : Link g layout h) : Flat.Fragment Φ A E D :=
  Flat.link f.first.fragment f.next.fragment

/-- Both components are recovered from their actual numbered tables.
Each component's existing certification checks its local token wires. -/
def recoverLink [DecidableEq τ] [DecidableEq Φ] (g : Reverse.Graph Φ ε A)
    (layout : Layout τ A X Z L E D sigs) (h : Flat.Serial.Graph Φ A X Z L E D sigs) :
    Option (Link g layout h) := do
  let first ← Reverse.recover g
  let next ← Translation.recover layout h
  return ⟨first, next⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta
