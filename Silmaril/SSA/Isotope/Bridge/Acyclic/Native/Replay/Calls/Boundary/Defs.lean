module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Boundary.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.CallPair.Defs

/-! # Effectful assembly at the exact outward boundary -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native.CallPairBoundary

open Region.Paper.BoundSimulation.Obstruction.PairSequencing
open RawBranch (Op)
open CallPair (U Packet)
open CallBoundary (input)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural Native.CallBoundary

def paired : Endpoint Op input Packet :=
  ⟨CallPair.paired, .let₁ (.pair CallPair.left_typed CallPair.right_typed) (.br rfl (.var rfl)),
    .let₁ _ (.br _)⟩

def sequenced : Endpoint Op input Packet :=
  ⟨CallPair.sequenced,
    .let₁ CallPair.left_typed (.let₁ (.let₁ (.var (i := 1) rfl) (.var (i := 0) rfl))
      (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))),
    .let₁ _ (.let₁ _ (.br _))⟩

/-- Exact code witness of the written pair-return region. -/
def pairCode : Code Op input Packet :=
  .let₁ ⟨.pair (.op .call (.bv 0)) (.let₁ (.bv 0) (.bv 0)),
    .pair (.op .bv) (.let₁ .bv .bv)⟩ (.br ⟨.bv 0, .bv⟩)

/-- The same two computations in separate binders, keeping the old input. -/
def seqCode : Code Op input Packet :=
  .let₁ ⟨.op .call (.bv 0), .op .bv⟩
    (.let₁ ⟨.let₁ (.bv 1) (.bv 0), .let₁ .bv .bv⟩
      (.br ⟨.pair (.bv 1) (.bv 0), .pair .bv .bv⟩))

end Silmaril.Isotope.LambdaSSA.Acyclic.Native.CallPairBoundary
