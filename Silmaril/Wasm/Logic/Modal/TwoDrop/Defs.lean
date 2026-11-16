module

public import Silmaril.Wasm.Logic.Modal.Thms
public import Silmaril.Wasm.Logic.Reachability

@[expose] public section
namespace Silmaril.Logic.Modal.Wasm.TwoDrop
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- Observations name actual configurations or the native Core terminal predicate. -/
inductive Atom where
  | middle | finish | terminal

def signature : Modal.Signature := ⟨Atom⟩

variable {H : Type}

/-- The first atom names the intermediate code; the last tests native termination. -/
def observations (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (a b : Val) : Model P host signature where
  valuation atom c := match atom with
    | .middle => c = Reachability.Wasm.middle s f vs a
    | .finish => c = Reachability.Wasm.finish s f vs
    | .terminal => c.Terminal
  point := Reachability.Wasm.start s f vs a b

end Silmaril.Logic.Modal.Wasm.TwoDrop
