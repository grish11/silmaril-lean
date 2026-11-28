module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Pair.Defs

/-! # A table with two and three duplicates

Five states in the order `b₀ a₀ b₁ a₁ b₂`. Class `a` has two duplicates
and class `b` has three. An `a` state relays, a `b` state returns outward
or repeats into an `a` state. Each jump chooses its target duplicate.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

/-- The state of the `d`-th of the two `a` duplicates. -/
def aShort (d : Fin 2) : Fin 5 := Fin.cases 1 (fun _ => 3) d

/-- The state of the `d`-th of the three `b` duplicates. -/
def bShort (d : Fin 3) : Fin 5 := Fin.cases 0 (Fin.cases 2 (fun _ => 4)) d

/-- The class of a state: `0` for `a`, `1` for `b`. -/
def shortClass : Fin 5 → Fin 2 := Fin.cases 1 pairClass

/-- The target duplicate of each jump. -/
structure ShortWiring where
  stay : Fin 2 → Fin 2
  enter : Fin 2 → Fin 3
  back : Fin 3 → Fin 2

def shortRows (q p : Program) (w : ShortWiring) : Fin 5 → Region signature.Instr :=
  Fin.cases (row 4 p (aShort (w.back 0)))
    (Fin.cases (relayRow 4 q (aShort (w.stay 0)) (bShort (w.enter 0)))
      (Fin.cases (row 4 p (aShort (w.back 1)))
        (Fin.cases (relayRow 4 q (aShort (w.stay 1)) (bShort (w.enter 1)))
          (fun _ => row 4 p (aShort (w.back 2))))))

theorem shortRows_typed (q p : Program) (w : ShortWiring) (i : Fin 5) :
    ValueBranches [State] (shortRows q p w i) [Silmaril.coprod Bit (States 4)] := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact row_typed 4 p _
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact relayRow_typed 4 q _ _
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact row_typed 4 p _
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact relayRow_typed 4 q _ _
        · exact row_typed 4 p _

/-- The table entered at state `i`. -/
def shortTable (q p : Program) (w : ShortWiring) (i : Fin 5) : Region signature.Instr :=
  dispatchEntered 4 (shortRows q p w) i

theorem shortTable_typed (q p : Program) (w : ShortWiring) (i : Fin 5) :
    ValueBranches [State] (shortTable q p w i) [Bit] :=
  dispatchEntered_typed (shortRows_typed q p w) i

/-- Jumps spread over the duplicates: the three `b` states repeat into
both `a` states, and the two `a` states enter different `b` states. -/
def ShortWiring.spread : ShortWiring :=
  ⟨fun d => d + 1, Fin.cases 2 (fun _ => 1), Fin.cases 1 (Fin.cases 0 (fun _ => 1))⟩

/-- Every jump targets the first duplicate. -/
def ShortWiring.first : ShortWiring := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
