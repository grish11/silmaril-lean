module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Paths.Thms
public import Silmaril.Semantics.Calco2019.Examples.Printing.TraceMonad.Thms

/-! # Productive iteration on nonempty trace sets -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Printing

variable {A X Y Z : Type u}

/-- Recursive returns print a nonempty word. Other observations impose no guard. -/
def ProductiveGuard (f : X → NonemptyTrace A (Y ⊕ Z)) : Prop :=
  TraceGuarded fun x => (f x).1

/-- The three-clause trace solution, with nonemptiness proved for guarded bodies. -/
def productiveIter (f : X → NonemptyTrace A (Y ⊕ X)) (hf : ProductiveGuard f) (x : X) :
    NonemptyTrace A Y :=
  ⟨greatestTrace (fun x => (f x).1) x, greatest_nonempty hf (fun x => (f x).2) x⟩

end Silmaril.Calco2019.Examples.Printing
