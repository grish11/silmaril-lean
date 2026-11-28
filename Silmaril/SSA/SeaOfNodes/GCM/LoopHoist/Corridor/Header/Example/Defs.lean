module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs

/-! # A local move of a latch-dependent addition -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg)
open Loop.MLIR.CF (Program TargetOp evalOp lower)
open LoopHoist.Dominance (stage)

def word : Width := ⟨8, by decide⟩
abbrev byte : Diamond.Ty Width := .value (.data word)
abbrev predicate : Diamond.Ty Width := .value .predicate
abbrev Inputs := [word, word, word]
abbrev Schedule : List (List (Diamond.Ty Width)) := [[byte], [byte], [byte], [predicate]]

/-- The nominated sum uses the first addition, or the intervening multiply
in the dependent variant. The two successor slots read distinct bindings. -/
def loop (dependent : Bool) : Program Inputs word word [] Schedule where
  preheader := .nil
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.arithmetic (.binary .muli))
        (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg .head) .nil))
        (.cons (.arithmetic (.binary .addi))
          (.cons (if dependent then .output (1 : Fin 2) .head else .output (0 : Fin 2) .head)
            (.cons (.arg (.tail (.tail .head))) .nil))
          (.cons (.ult word)
            (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil)) .nil)))
  phiInputs
    | .entry => .cons (.arg .head) .nil
    | .backedge => .cons (.output (2 : Fin 4) .head) .nil
  predicate := .output (3 : Fin 4) .head
  result := .output (1 : Fin 4) .head

def input (start limit stride : BitVec 8) : Env Inputs :=
  .cons start (.cons limit (.cons stride .nil))

def selected? (dependent : Bool) : Option (Point (SourceLabel word word)) := do
  let ⟨_, binding⟩ ← findBinding 2 0 headerOrigins ((lower (loop dependent)).block .header)
  chooseCut? (loop dependent) binding.operands binding.uses

/-- Show the binding order in the actual typed CF header. -/
def opOrder : {Γ : List Width} → Block TargetOp (SourceLabel word word) Γ [word] → List String
  | _, .terminator _ => []
  | _, .letOp op _ rest =>
    let name := match op with
      | .original (.constant _) => "constant"
      | .original (.binary _ .addi) | .addi _ => "addi"
      | .original (.binary _ .subi) => "subi"
      | .original (.binary _ .muli) => "muli"
      | .ult _ => "ult"
      | .slt _ => "slt"
    name :: opOrder rest

/-- The actual selected block and cut, opcode order before and after, and
the emitted program's results at CF fuels three, four and five. -/
def observe (dependent : Bool) :
    Option (Nat × Nat) × List String × Option (List String × List (Option Nat)) :=
  ((selected? dependent).map (fun cut => (stage cut.block, cut.cut)),
    opOrder ((lower (loop dependent)).block .header),
    (pickAndMove? (loop dependent) 2).map fun (_, cfg) =>
      (opOrder (cfg.block .header), [3, 4, 5].map fun fuel =>
        (cfg.run evalOp fuel (input 2 6 1)).map (fun env => (env.get .here).toNat)))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example
