module

public import Silmaril.Logic.ModalMu.Thms

@[expose] public section
namespace Silmaril.Logic.ModalMu

/-- A finite action-labelled path ending in the target, including length zero. -/
inductive FiniteReach {W : Type} (step : W → W → Prop) (target : Set W) : W → Prop
  | here {w} : w ∈ target → FiniteReach step target w
  | next {w v} : step w v → FiniteReach step target v → FiniteReach step target w

def reach {S : Signature} (a : S.Action) (p : S.Atom) : Formula S 0 :=
  .mu (.disj (.pos p) (.diamond a (.var 0)))

def forever {S : Signature} (a : S.Action) : Formula S 0 :=
  .nu (.diamond a (.var 0))

end Silmaril.Logic.ModalMu
