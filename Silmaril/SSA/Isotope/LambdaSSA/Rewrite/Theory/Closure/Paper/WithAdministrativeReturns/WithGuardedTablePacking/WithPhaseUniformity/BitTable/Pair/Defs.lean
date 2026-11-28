module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Relay.Defs

/-! # A table with two duplicated classes

Four states in the order `a₀ b₀ a₁ b₁`. An `a` state relays: it runs `q`,
repeats into an `a` state on one reply side and enters a `b` state on the
other. A `b` state runs `p`, returns outward, or repeats into an `a`
state. Which duplicate each jump targets is free, per source state.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

/-- The state of the `d`-th duplicate of class `a`. -/
def aState (d : Fin 2) : Fin 4 := Fin.cases 0 (fun _ => 2) d

/-- The state of the `d`-th duplicate of class `b`. -/
def bState (d : Fin 2) : Fin 4 := Fin.cases 1 (fun _ => 3) d

/-- The class of a state: `0` for `a`, `1` for `b`. -/
def pairClass : Fin 4 → Fin 2 := Fin.cases 0 (Fin.cases 1 (Fin.cases 0 (fun _ => 1)))

/-- For each duplicate, the duplicate it targets: where an `a` state
repeats within its class, where it enters class `b`, and where a `b`
state repeats into class `a`. -/
structure Wiring where
  stay : Fin 2 → Fin 2
  enter : Fin 2 → Fin 2
  back : Fin 2 → Fin 2

def pairRows (q p : Program) (w : Wiring) : Fin 4 → Region signature.Instr :=
  Fin.cases (relayRow 3 q (aState (w.stay 0)) (bState (w.enter 0)))
    (Fin.cases (row 3 p (aState (w.back 0)))
      (Fin.cases (relayRow 3 q (aState (w.stay 1)) (bState (w.enter 1)))
        (fun _ => row 3 p (aState (w.back 1)))))

theorem pairRows_typed (q p : Program) (w : Wiring) (i : Fin 4) :
    ValueBranches [State] (pairRows q p w i) [Silmaril.coprod Bit (States 3)] := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact relayRow_typed 3 q _ _
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact row_typed 3 p _
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact relayRow_typed 3 q _ _
      · exact row_typed 3 p _

/-- The table entered at state `i`. -/
def pairTable (q p : Program) (w : Wiring) (i : Fin 4) : Region signature.Instr :=
  dispatchEntered 3 (pairRows q p w) i

theorem pairTable_typed (q p : Program) (w : Wiring) (i : Fin 4) :
    ValueBranches [State] (pairTable q p w i) [Bit] :=
  dispatchEntered_typed (pairRows_typed q p w) i

/-- Each duplicate targets the other duplicate of the class it jumps to. -/
def Wiring.crossed : Wiring := ⟨fun d => d + 1, fun d => d + 1, fun d => d + 1⟩

/-- Each duplicate targets the first duplicate. -/
def Wiring.first : Wiring := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
