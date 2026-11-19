module

public import Silmaril.Semantics.Region.Semantic.Thms
public import Silmaril.Semantics.Region.Thms

@[expose] public section
namespace Silmaril.Semantics.Region.Examples

/-- Benign state machine: entry restricts a formerly unconstrained indirect
selector before the internal transfer uses it. -/
inductive Edge : Nat × Bool → List Empty → Nat × Bool → Prop where
  | restrict (b : Bool) : Edge (0, b) [] (1, true)
  | indirect (b : Bool) : Edge (1, b) [] (if b then 2 else 3, b)

def machine : TransitionSystem (Nat × Bool) Nat Empty Empty := ⟨Prod.fst, Edge, fun _ _ => False⟩
def support (l : Nat) : Prop := l = 0 ∨ l = 1
def domain (s : Nat × Bool) : Prop := s.1 = 0 ∨ s.2 = true

def loop : TransitionSystem Unit Nat Empty Empty where
  pc _ := 0
  step s es t := s = t ∧ es = []
  halt _ _ := False

/-- Segment witnesses forced by the entry; erasure discards their compatibility. -/
def witnessModel : SegmentRegionModel Unit Unit Bool Bool where
  SegBB _ _ _ := True
  BB _ _ s e _ := s = e
  SR _ _ ss e _ := ss = {e}
  SR' _ _ ss e _ := ss = {e}
  Reg _ _ ss e _ := ss = {e}
end Silmaril.Semantics.Region.Examples
