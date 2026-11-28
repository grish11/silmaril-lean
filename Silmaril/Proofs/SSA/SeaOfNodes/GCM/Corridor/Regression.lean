module

import Silmaril.SSA.SeaOfNodes.GCM.Corridor.Thms
meta import Silmaril.SSA.SeaOfNodes.GCM.Corridor.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.Corridor.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (i1)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Corridor

private inductive Label : List Width → Type
  | preheader : Label [i1]
  | outer : Label [i1]
  | inner : Label [i1]
  | innerLatch : Label [i1]
  | outerLatch : Label [i1]
  | exit : Label [i1]
  deriving DecidableEq

private def target (label : Label [i1]) : Target Label := ⟨_, label⟩
private def block (label : Label [i1]) : BlockId Label := some (target label)

private def cfg : Cfg (fun _ _ => Unit) Label [i1] [i1] where
  entry := .terminator (.br ⟨.preheader, .cons .here .nil⟩)
  block
    | .preheader => .letOp (w := i1) () .nil (.terminator (.br ⟨.outer, .cons .here .nil⟩))
    | .outer => .terminator (.condBr .here ⟨.inner, .cons .here .nil⟩ ⟨.exit, .cons .here .nil⟩)
    | .inner => .terminator
        (.condBr .here ⟨.innerLatch, .cons .here .nil⟩ ⟨.outerLatch, .cons .here .nil⟩)
    | .innerLatch => .letOp (w := i1) () .nil (.letOp (w := i1) () .nil
        (.terminator (.condBr .here ⟨.inner, .cons .here .nil⟩
          ⟨.inner, .cons (.there .here) .nil⟩)))
    | .outerLatch => .terminator (.br ⟨.outer, .cons .here .nil⟩)
    | .exit => .terminator (.ret (.cons .here .nil))

private def blocks : List (Target Label) :=
  [.innerLatch, .inner, .outer, .preheader, .outerLatch, .exit, .innerLatch].map target

private def number : BlockId Label → Nat
  | none => 0
  | some ⟨_, .preheader⟩ => 1
  | some ⟨_, .outer⟩ => 2
  | some ⟨_, .inner⟩ => 3
  | some ⟨_, .innerLatch⟩ => 4
  | some ⟨_, .outerLatch⟩ => 5
  | some ⟨_, .exit⟩ => 6

private theorem number_injective : Function.Injective number := by
  rintro (_ | ⟨_, a⟩) (_ | ⟨_, b⟩)
  · intro _
    rfl
  · cases b <;> simp [number]
  · cases a <;> simp [number]
  · cases a <;> cases b <;> simp [number]

private def tree? := Dominance.Tree.Synthesis.synthesize? cfg blocks number number_injective

private def phiReads : List (Use Label) :=
  [.phi (block .innerLatch) .onTrue 0, .phi (block .innerLatch) .onFalse 0]

-- Both slots target the same header, but transfer distinct local operands.
example : Dominance.occurrences cfg (block .innerLatch) =
    [(.onTrue, target .inner), (.onFalse, target .inner)] := by cbv
example : phiReads.map (Use.point? cfg) =
    [some ⟨block .innerLatch, 2⟩, some ⟨block .innerLatch, 2⟩] := by cbv

#guard (tree?.bind fun tree => (LoopForest.forest? tree.1 blocks).map fun loops =>
    [.preheader, .outer, .inner, .innerLatch].map fun label => LoopForest.depth tree.1 loops (block label)) ==
    some [0, 1, 2, 2]
#guard (tree?.map fun tree =>
    (addresses (tree.1.address (block .preheader)) (tree.1.address (block .innerLatch))).map List.length) ==
    some [4, 3, 2, 1]

private def observe (point : Point Label) : Nat × Nat := (number point.block, point.cut)

private def compare (defs : List (Point Label)) (reads : List (Use Label))
    (inventory : List (Target Label) := blocks) :
    Option (Option (Nat × Nat) × Option (Nat × Nat)) :=
  tree?.map fun tree =>
    ((Corridor.choosePlacement tree.1 inventory defs reads).map observe,
      (LoopForest.choosePlacement tree.1 inventory defs reads).map observe)

-- Loop depth wins over the deeper address of the late endpoint.
#guard (chooseSynthesized? cfg blocks number number_injective [⟨block .preheader, 1⟩] phiReads).map
    observe == some (1, 1)
#guard compare [⟨block .preheader, 1⟩] phiReads == some (some (1, 1), some (1, 1))

-- At depth two the deepest block wins, then the first legal cut in that block.
#guard compare [⟨block .inner, 0⟩] phiReads == some (some (4, 0), some (4, 0))
#guard compare [⟨block .innerLatch, 1⟩] phiReads == some (some (4, 1), some (4, 1))

-- A read before the operand at the same block leaves no local cut.
#guard compare [⟨block .innerLatch, 1⟩] (.ordinary ⟨block .innerLatch, 0⟩ :: phiReads) ==
    some (none, none)
#guard compare [⟨block .innerLatch, 1⟩] [.ordinary ⟨block .outerLatch, 0⟩] == some (none, none)
#guard compare [] [.phi (block .innerLatch) .jump 0] == some (none, none)

-- The same forest refuses an inventory that omits the reachable inner latch.
#guard compare [] phiReads [target .preheader, target .outer, target .inner,
    target .outerLatch, target .exit] == some (none, none)
#guard compare [⟨block .preheader, 1⟩] [] == some (some (6, 0), some (6, 0))

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.Corridor.Regression
