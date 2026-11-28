module

public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Defs
public import Silmaril.SSA.PhiView.Defs

/-! # Pack a numbered θ body for the existing one-block λSSA CFG -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational

open Isotope (Value)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics (Env)

universe u v w x y

variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {carried ports : List (PortType V S)} {sigs : List (List (PortType V S))}

abbrev Packed (ports : List (PortType V S)) : Silmaril.Ty (PortType V S) :=
  PhiView.packedType (ports.map Silmaril.Ty.base)

/-- An instruction contains the actual numbered acyclic body, with its
return ports fixed to its control selector and carried packet. -/
abbrev Instruction (Op : Dialect.{u,v} V S) (carried : List (PortType V S)) :=
  Σ sigs, RVSDG.Graph Op carried [] sigs (RVSDG.Theta.BodyResults carried)

instance : HasTy (Instruction Op carried) (Silmaril.Ty (PortType V S)) where
  src _ := Packed carried
  trg _ := .coprod (Packed carried) (Packed carried)

def step (g : RVSDG.Theta.Graph Op carried sigs) :
    LambdaSSA.Theta.Step (Instruction Op carried) (Packed carried) :=
  ⟨⟨sigs, g.body⟩, rfl, rfl⟩

/-- Enter the single header at local label zero with the input packet.
The header uses label zero for feedback and label one for external exit zero. -/
def loop {Φ : Type y} (header : Region Φ) : Region Φ :=
  .cfg (.br 0 (.var 0)) 1 (fun _ => header)

/-- The existing CFG jumps to local label zero at entry and on continuation.
Its other branch exits with the whole packet. -/
def lower (g : RVSDG.Theta.Graph Op carried sigs) : Region (Instruction Op carried) :=
  loop (LambdaSSA.Theta.block (step g).op)

variable (m : Model.{u,v,w} Op)

abbrev Atom := (p : PortType V S) × m.Val p

def pack : {ports : List (PortType V S)} → Tuple m.Val ports → Value (Atom m)
  | _, .nil => .unit
  | _, .cons a rest => .pair (.atom ⟨_, a⟩) (pack rest)

def inputEnv (input : Tuple m.Val carried) : Env (Atom m) :=
  Isotope.LambdaSSA.Semantics.extend (fun _ => .unit) (pack m input)

/-- Decode the selector emitted by one numbered body activation. -/
def split : Tuple m.Val (RVSDG.Theta.BodyResults carried) → Bool × Tuple m.Val carried
  | .cons tag result => (tag.down.val != 0, result)

def choice (result : Bool × Tuple m.Val carried) : Value (Atom m) :=
  if result.1 then .inr (pack m result.2) else .inl (pack m result.2)

/-- Only one body activation is executed by the primitive. Restarts are
ordinary λSSA jumps. This interpretation leaves ambient state alone. -/
def instruction {σ : Type x} (op : Instruction Op carried) (arg : Value (Atom m))
    (start : σ) (ret : Value (Atom m)) (finish : σ) : Prop :=
  ∃ input : Tuple m.Val carried,
    arg = pack m input ∧ ret = choice m (split m (op.2.run m input)) ∧ finish = start

/-- Bounded evaluation on typed packets for this emitted CFG. Each header
visit costs one unit, including the terminating visit. -/
def runFuel (g : RVSDG.Theta.Graph Op carried sigs) :
    Nat → Tuple m.Val carried → Option (Tuple m.Val carried)
  | 0, _ => none
  | fuel + 1, input =>
    let result := split m (g.body.run m input)
    if result.1 then runFuel g fuel result.2 else some result.2

end Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational
