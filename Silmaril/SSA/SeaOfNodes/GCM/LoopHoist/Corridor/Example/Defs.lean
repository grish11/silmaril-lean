module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Defs

/-! # A nominated loop binding with two possible placement profiles -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example

open Silmaril.MLIR.Arith (Env Width)
open Loop.MLIR.CF (Program evalOp lower)
open LoopHoist.Dominance (stage)

def word : Width := ⟨8, by decide⟩
abbrev byte : Diamond.Ty Width := .value (.data word)
abbrev predicate : Diamond.Ty Width := .value .predicate
abbrev Inputs := [word, word, word]
abbrev entrySigs : List (List (Diamond.Ty Width)) := [[byte], [byte]]
abbrev headerSigs : List (List (Diamond.Ty Width)) := [[byte], [byte], [predicate], [byte]]

/-- The prefix computes latch plus stride. The nominated second binding
doubles the captured stride, or uses that prefix result in the dependent variant. -/
def loop (dependent : Bool) : Program Inputs word word entrySigs headerSigs where
  preheader :=
    .cons (.arithmetic (.constant (1 : BitVec 8))) .nil
      (.cons (.arithmetic (.binary .addi))
        (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.arithmetic (.binary .addi))
        (.cons (if dependent then .output (0 : Fin 1) .head else .arg (.tail (.tail .head)))
          (.cons (.arg (.tail (.tail .head))) .nil))
        (.cons (.ult word)
          (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil))
          (.cons (.arithmetic (.binary .addi))
            (.cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.output (1 : Fin 2) .head) .nil
    | .backedge => .cons (.output (3 : Fin 4) .head) .nil
  predicate := .output (2 : Fin 4) .head
  result := .output (1 : Fin 4) .head

def input (start limit stride : BitVec 8) : Env Inputs :=
  .cons start (.cons limit (.cons stride .nil))

/-- Show the actual ranked cut even when the preheader emitter refuses it. -/
def selected? (dependent : Bool) : Option (Point (SourceLabel word word)) := do
  let ⟨_, binding⟩ ← findBinding 1 0 headerOrigins ((lower (loop dependent)).block .header)
  chooseCut? (loop dependent) binding.operands binding.uses

/-- The selected block number and cut, followed by emitted binding counts
and results at CF fuels three, four and five when a move is admitted. -/
def observe (dependent : Bool) : Option (Nat × Nat) × Option (Nat × Nat × List (Option Nat)) :=
  ((selected? dependent).map (fun cut => (stage cut.block, cut.cut)),
    (Corridor.pickAndHoist? (loop dependent) 1).map fun (_, output) =>
      ((shape output.2 none).bindings, (shape output.2 (some ⟨_, .header⟩)).bindings,
        [3, 4, 5].map fun fuel => (output.2.run evalOp fuel (input 2 8 1)).map
          (fun env => (env.get .here).toNat)))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example
