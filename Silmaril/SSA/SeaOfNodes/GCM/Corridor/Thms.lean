module

public import Silmaril.SSA.SeaOfNodes.GCM.Corridor.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.Corridor.Correctness
import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Corridor

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Dominance (checkClosed)
open EarlyPlacement (earlyBound?)
open LatePlacement (lateBound?)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {tree : DominatorTree cfg}
variable {blocks : List (Target Label)} {operands : List (Point Label)} {uses : List (Use Label)}
variable {early late : BlockId Label} {loops : List (LoopForest.HeaderLoop Label)}
variable [DecidableEq (Target Label)]

/-- The address walk includes exactly the prefixes of late extending early. -/
theorem mem_addresses_iff (early late address : List Nat) :
    address ∈ addresses early late ↔ List.IsPrefix early address ∧ List.IsPrefix address late :=
  Proofs.SSA.SeaOfNodes.GCM.Corridor.mem_addresses_iff early late address

/-- The corridor keeps the exact list of accepted cuts, including its order. -/
theorem acceptedCorridorCuts_eq (complete : tree.Complete) (closed : checkClosed cfg blocks = true)
    (earlyFound : earlyBound? tree operands = some early) (lateFound : lateBound? tree blocks uses = some late) :
    acceptedCorridorCuts tree blocks early late operands uses = acceptedCuts tree blocks operands uses :=
  Proofs.SSA.SeaOfNodes.GCM.Corridor.acceptedCorridorCuts_eq complete closed earlyFound lateFound

/-- Under complete tree evidence both choosers return the same cut or refusal.
This includes equal-score cut order and the empty-use case. -/
theorem choosePlacement_eq (complete : tree.Complete) :
    choosePlacement tree blocks operands uses = LoopForest.choosePlacement tree blocks operands uses :=
  Proofs.SSA.SeaOfNodes.GCM.Corridor.choosePlacement_eq complete

/-- Selecting in the computed corridor preserves minimum natural-loop depth
and the deepest dominator tie-break. -/
theorem choosePlacement_minimal (complete : tree.Complete)
    (admitted : LoopForest.forest? tree blocks = some loops) {chosen other : Point Label}
    (found : choosePlacement tree blocks operands uses = some chosen)
    (member : other ∈ candidateCuts cfg blocks) (checked : checkPlacement tree operands uses other = true) :
    LoopForest.depth tree loops chosen.block ≤ LoopForest.depth tree loops other.block ∧
      (LoopForest.depth tree loops chosen.block = LoopForest.depth tree loops other.block →
        (tree.address other.block).length ≤ (tree.address chosen.block).length) :=
  LoopForest.choosePlacement_minimal admitted ((choosePlacement_eq complete).symm.trans found)
    member checked

/-- The synthesized entry point agrees with invoking the existing chooser
after the same synthesis, including synthesis refusal. -/
theorem chooseSynthesized?_eq (number : BlockId Label → Nat) (injective : Function.Injective number) :
    chooseSynthesized? cfg blocks number injective operands uses =
      (Dominance.Tree.Synthesis.synthesize? cfg blocks number injective).bind fun tree =>
        LoopForest.choosePlacement tree.1 blocks operands uses :=
  Proofs.SSA.SeaOfNodes.GCM.Corridor.chooseSynthesized?_eq number injective

end Silmaril.SSA.SeaOfNodes.GCM.Corridor
