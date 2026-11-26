module

import Silmaril.SSA.PEG.Bridge.MLIR.Thms

namespace Silmaril.SSA.PEG.Bridge.Tests

open RVSDG (Tuple)
open Silmaril.SSA.RVSDG.MLIR

private abbrev num : Ty Unit := .data ()

private inductive Instr : InstructionSet.{0,0} Unit
  | ten : Instr [] num
  | mix : Instr [num, .count, num] num
  | sub : Instr [num, num] num

private def model : TotalModel Instr where
  carrier _ := Nat
  run
    | .ten, .nil => (10 : Nat)
    | .mix, .cons x (.cons k (.cons y .nil)) => Nat.add (Nat.mul x k.down) y + 6
    | .sub, .cons x (.cons y .nil) => Nat.sub x y

private abbrev params : List (Ty Unit) := [.bool, num, .count]
private abbrev results : List (Ty Unit) := [num, num, num, .count, num]
private def sorts (i : Fin 7) : Ty Unit :=
  if i.val = 0 then .bool else if i.val = 2 then .count else num

private def graph : Graph Instr params results 7 0 where
  forest := ⟨Fin.elim0⟩
  sort := sorts
  node
    | ⟨0, _⟩ => .ofLabel (.param .head) .nil
    | ⟨1, _⟩ => .ofLabel (.param (.tail .head)) .nil
    | ⟨2, _⟩ => .ofLabel (.param (.tail (.tail .head))) .nil
    | ⟨3, _⟩ => .ofLabel (.op .ten) .nil
    | ⟨4, _⟩ => .ofLabel (.op .mix) (.cons ⟨1, rfl⟩ (.cons ⟨2, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))
    | ⟨5, _⟩ => .ofLabel (.op .sub) (.cons ⟨4, rfl⟩ (.cons ⟨3, rfl⟩ .nil))
    | ⟨6, _⟩ => .ofLabel .phi (.cons ⟨0, rfl⟩ (.cons ⟨5, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))
    | ⟨i + 7, h⟩ => False.elim (by omega)
  roots := .cons ⟨6, rfl⟩ (.cons ⟨4, rfl⟩ (.cons ⟨6, rfl⟩
    (.cons ⟨2, rfl⟩ (.cons ⟨5, rfl⟩ .nil))))

private theorem ordered : Ordered graph := by decide

private def input (flag : Bool) : Tuple model.toPEG.Value params :=
  .cons ⟨flag⟩ (.cons (4 : Nat) (.cons ⟨2⟩ .nil))

private def expected (answer : Nat) : Tuple model.toPEG.Value results :=
  .cons answer (.cons (18 : Nat) (.cons answer (.cons ⟨2⟩ (.cons (8 : Nat) .nil))))

private def runRVSDG (flag : Bool) : Tuple model.toPEG.Value results :=
  fromPorts results ((translate graph ordered).2.run model.toRVSDG (toPorts (input flag)))

private def runMLIR (flag : Bool) : Tuple model.toPEG.Value results :=
  fromPorts results (Regionless.ofAssignment (F := model.toRVSDG.Val) results (fun i =>
    (translateMLIR graph ordered i).denote model.toMLIR
      (Regionless.toAssignment params (toPorts (F := model.toRVSDG.Val) (input flag)))))

example : runRVSDG true = expected 8 := rfl
example : runRVSDG false = expected 4 := rfl
example : runMLIR true = expected 8 := rfl
example : runMLIR false = expected 4 := rfl

private def producers {past : List (List (ValuePort Unit))} :
    {ts : List (ValuePort Unit)} → RVSDG.Wires (valuePorts params) past ts → List (Option Nat)
  | _, .nil => []
  | _, .cons wire rest => wire.producer :: producers rest

-- Both repeated operands keep the same numbered producer in the target graph.
example : producers ((translate graph ordered).2.nodes ⟨4, by decide⟩).inputs =
    [some 1, some 2, some 1] := rfl

private noncomputable def runPEG (flag : Bool) :
    Tuple (fun t => Option (model.toPEG.Value t)) results :=
  graph.observe model.toPEG (graph.denote model.toPEG (input flag) ordered.demandWellFounded) Fin.elim0

example : runPEG true = (expected 8).map (fun _ => some) := by
  rw [runPEG, observe_translate graph ordered]
  rfl

example : runPEG false = (expected 4).map (fun _ => some) := by
  rw [runPEG, observe_translateMLIR graph ordered]
  rfl

-- Changing a primitive to read its own output keeps the wiring typed.
private def selfEdge : Graph Instr [] [num] 1 0 where
  forest := ⟨Fin.elim0⟩
  sort _ := num
  node _ := .ofLabel (.op .sub) (.cons ⟨0, rfl⟩ (.cons ⟨0, rfl⟩ .nil))
  roots := .cons ⟨0, rfl⟩ .nil

example : ¬ Ordered selfEdge := by decide

-- The actual primitive equation is strict, even when its primitive ignores all arguments.
private def ignoresArgs : Interpretation Instr :=
  ⟨model.carrier, fun
    | .ten, _ => some (1 : Nat)
    | .mix, _ => some (1 : Nat)
    | .sub, _ => some (1 : Nat)⟩

private def missingRhs (s : Fin [num, num].length) : Option (ignoresArgs.Value [num, num][s]) :=
  Fin.cases (motive := fun i => Option (ignoresArgs.Value [num, num][i])) (some (7 : Nat)) (fun _ => none) s

example : (Label.op Instr.sub : Label Instr [] (Fin 0) [num, num] num).interpret
    ignoresArgs .nil Fin.elim0 (fun s _ _ => missingRhs s) = none :=
  interpret_op_eq_none ignoresArgs .nil Fin.elim0 .sub _ 1 rfl

-- The Figure 11 conditional still reads only the selected arm.
private def unselectedBottom (s : Fin [Ty.bool, num, num].length) :
    Option (model.toPEG.Value [Ty.bool, num, num][s]) :=
  Fin.cases (motive := fun i => Option (model.toPEG.Value [Ty.bool, num, num][i]))
    (some ⟨true⟩) (Fin.cases (some (7 : Nat)) (fun _ => none)) s

example : (Label.phi : Label Instr [] (Fin 0) [.bool, num, num] num).interpret
    model.toPEG .nil Fin.elim0 (fun s _ _ => unselectedBottom s) = some (7 : Nat) := rfl

end Silmaril.SSA.PEG.Bridge.Tests
