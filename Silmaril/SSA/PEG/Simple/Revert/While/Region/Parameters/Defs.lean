module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs

/-! # Typed parameter bindings for region schedules -/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars more : List (Ty Data)} {result t : Ty Data} {n l : Nat}

/-- Concatenate a slice's working slots and its retained scope. -/
def appendScope {F : Ty Data → Type w} :
    {vars : List (Ty Data)} → Tuple F vars → Tuple F more → Tuple F (vars ++ more)
  | _, .nil, tail => tail
  | _, .cons head rest, tail => .cons head (appendScope rest tail)

structure ParameterRow (g : Graph P params [result] n l) (t : Ty Data) where
  ref : Ref g.sort t
  input : Port params t
  wired : nodeAt g ref = .ofLabel (.param input) .nil

def parameterRows (g : Graph P params [result] n l) : List (Sigma (ParameterRow g)) :=
  (List.finRange n).filterMap fun i =>
    match row : g.node i with
    | ⟨_, .param input, args⟩ =>
      match args with
      | .nil => some ⟨g.sort i, ⟨Ref.ofId g.sort i, input, row⟩⟩
    | _ => none

def parameterTuple {g : Graph P params [result] n l} :
    (rows : List (Sigma (ParameterRow g))) → Tuple (ParameterRow g) (rows.map Sigma.fst)
  | [] => .nil
  | head :: rest => .cons head.2 (parameterTuple rest)

structure Parameters (g : Graph P params [result] n l) where
  types : List (Ty Data)
  bindings : Tuple (ParameterRow g) types

def Parameters.infer (g : Graph P params [result] n l) : Parameters g :=
  let rows := parameterRows g
  ⟨_, parameterTuple rows⟩

def Parameters.refs {g : Graph P params [result] n l} (captures : Parameters g) :
    Tuple (Ref g.sort) captures.types :=
  captures.bindings.map fun _ row => row.ref

/-- Load each parameter row from its label's typed input port. Distinct
rows may name the same input and unused input ports need no row. -/
def Parameters.inputs {g : Graph P params [result] n l} (captures : Parameters g) :
    Tuple (Port params) captures.types :=
  captures.bindings.map fun _ row => row.input

/-- Propose an order and replay it against the typed primitive slice. -/
def Schedule.inferPrimitive (g : Graph P params [result] n l)
    (scope : Tuple (Ref g.sort) vars) (roots : Tuple (Ref g.sort) more) :
    Option (Schedule g false roots scope) := do
  let some order := scopedOrder g scope roots | none
  Schedule.check g roots order scope

end Silmaril.SSA.PEG.Simple.Revert.While.Region
