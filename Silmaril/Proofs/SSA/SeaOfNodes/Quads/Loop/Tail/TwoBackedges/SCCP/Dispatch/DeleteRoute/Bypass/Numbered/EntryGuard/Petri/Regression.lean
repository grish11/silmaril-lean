module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Thms
meta import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri

open Bypass.MLIR.CF.Example (entry facts program regs word width)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.Diamond (Val)
open Silmaril.MLIR.Arith (Width)
open Relation (ReflTransGen)
open RVSDG (Tuple)
open RVSDG.NestedTheta (Graph Term)
open RVSDG.NestedTheta.Petri (Fire Finishes Step result GraphMarking Marking finished pending activate primitive route)
open RVSDG.Petri (Tokens read)
open Blocks (Bank)

private def assumptions := facts (.constant ⟨true⟩)
private abbrev runtime := Join.model model
private def target : Target regs width := (compile program assumptions).toOption.get (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Execute one firing in the fixtures' ordered schedule. The proof
component records the actual firing. The fixtures finish without a restart. -/
private def fireNext :
    {args outs : List (Diamond.Ty Width)} →
    {past sigs : List (List (Diamond.Ty Width))} →
    (term : Term (Join.Opcode Op) args past sigs outs) → (input : Tuple runtime.Val args) →
    (tokens : Tokens runtime.Val past) → (before : Marking runtime term) →
    Option {after : Marking runtime term // Fire runtime term input tokens before after}
  | _, _, _, _, .ret _, _, _, _ => none
  | _, _, _, _, .bind node children rest, input, tokens, before =>
    match before with
    | (.done output, tail) =>
      (fireNext rest input (tokens.snoc (output.map fun _ => some)) tail).map fun fired =>
        ⟨(.done output, fired.1), .later fired.2⟩
    | (.pending, tail) =>
      match ready : read node.inputs input tokens with
      | none => none
      | some operands =>
        match published : primitive runtime node.kind operands with
        | some output => some ⟨(.done output, tail), .primitive ready published⟩
        | none =>
          match selected : activate runtime node.kind operands with
          | none => none
          | some (arm, bank) => some
              ⟨(.waiting arm (bank, pending runtime (children arm)), tail), .enter ready selected⟩
    | (.waiting arm (bank, child), tail) =>
      match completed : finished runtime (past := []) (children arm) bank PUnit.unit child with
      | none =>
        (fireNext (children arm) bank PUnit.unit child).map fun fired =>
          ⟨(.waiting arm (bank, fired.1), tail), .advance fired.2⟩
      | some packet =>
        match released : route runtime node.kind arm packet with
        | .inl output => some ⟨(.done output, tail), .commit completed released⟩
        | .inr _ => none

private def trace (target : Target regs width) (input : Bank (regs := regs) model) :
    Nat → (before : GraphMarking runtime target.2) →
    Option {after : GraphMarking runtime target.2 // ReflTransGen (Step runtime target.2 input) before after}
  | 0, before => some ⟨before, .refl⟩
  | fuel + 1, before => do
    let fired ← fireNext target.2.toTerm input PUnit.unit before
    let remaining ← trace target input fuel fired.1
    pure ⟨remaining.1, ReflTransGen.head fired.2 remaining.2⟩

private def report (target : Target regs width) (input : Bank (regs := regs) model)
    (firings : Nat) : Option Nat := do
  let completed ← trace target input firings (RVSDG.NestedTheta.Petri.initial runtime target.2)
  let packet ← result runtime target.2 input completed.1
  let value : Word width := packet.get .head
  pure value.toNat

#guard report target (entry true true) 20 = some 99
#guard report target (entry true false) 16 = some 7
#guard (report target (entry true true) 19).isNone
#guard (report target (entry true false) 15).isNone

private theorem compiled : compile program assumptions = .ok target := rfl

private theorem covered_completion :
    Finishes runtime target.2 (entry true true) (.cons (99 : Word width) .nil) :=
  (compile_finishes_iff compiled _ _).mpr ⟨5, rfl⟩

private theorem uncovered_completion :
    Finishes runtime target.2 (entry true false) (.cons (7 : Word width) .nil) :=
  (compile_finishes_iff compiled _ _).mpr ⟨5, rfl⟩

example : ∃ fuel, target.2.run runtime fuel (entry true true) = some (.cons (99 : Word width) .nil) :=
  (finishes_iff_numbered target _ _).mp covered_completion

example : ∃ fuel, target.2.run runtime fuel (entry true false) = some (.cons (7 : Word width) .nil) :=
  (finishes_iff_numbered target _ _).mp uncovered_completion

example {packet : Tuple (Val Word) [.value word]} {final : GraphMarking runtime target.2}
    (reachable : ReflTransGen (Step runtime target.2 (entry true false))
    (RVSDG.NestedTheta.Petri.initial runtime target.2) final)
    (completed : result runtime target.2 (entry true false) final = some packet) :
    packet = .cons (7 : Word width) .nil := by
  have success : compile program assumptions = .ok target := rfl
  have numbered := EntryGuard.compile_run success 1 (entry true false)
  exact completed_packet_eq target (entry true false) ⟨final, reachable, completed⟩ numbered

-- The retained true route stays in the loop. The original false route stops.
private def trueLoops : Program Op regs word :=
  { program with feedback := fun side => if side then [] else program.feedback false }

private def retained : Checked model trueLoops assumptions :=
  (Backends.Worklist.admit model trueLoops assumptions).toOption.get (by rfl)

private abbrev guardedLoop : Target regs width := EntryGuard.lower retained

#guard report guardedLoop (entry true false) 16 = some 7

private theorem bypass_header_no_return (side : Bool) (budget : Nat) :
    (Bypass.bypass retained).runFrom model budget 1 (entry true side) = none := by
  induction budget using Nat.strong_induction_on with
  | ind budget smaller =>
    match budget with
    | 0 | 1 => rfl
    | fuel + 2 =>
      change (Bypass.bypass retained).runFrom model fuel 1 (entry true side) = none
      exact smaller fuel (by omega)

private theorem specialized_no_return (side : Bool) (fuel : Nat) :
    (Bypass.Numbered.lower retained).run runtime fuel (entry true side) = none := by
  rw [Bypass.Numbered.lower_run retained fuel (entry true side)]
  change ((Bypass.bypass retained).runFrom model (2 * fuel + 1) 1 (entry true side)).map _ = none
  rw [bypass_header_no_return]
  rfl

-- On this very input the unselected specialization has no finite completion.
example : ∀ packet, ¬ Finishes runtime (Bypass.Numbered.lower retained) (entry true false) packet :=
  (no_completion_iff_numbered ⟨_, Bypass.Numbered.lower retained⟩ _).mpr (specialized_no_return false)

example : ∀ packet, ¬ Finishes runtime guardedLoop.2 (entry true true) packet := by
  apply (no_completion_iff_numbered guardedLoop _).mpr
  intro fuel
  have selected : guardedLoop.2.run runtime fuel (entry true true) =
      (Bypass.Numbered.lower retained).run runtime fuel (entry true true) := by
    rw [guardedLoop, EntryGuard.lower, EntryGuard.attach_run, EntryGuard.selector_run]
    rfl
  exact selected.trans (specialized_no_return true fuel)

example : Finishes runtime guardedLoop.2 (entry true false) (.cons (7 : Word width) .nil) :=
  (compile_finishes_iff (target := guardedLoop) (p := trueLoops) (facts := assumptions) rfl _ _).mpr ⟨5, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri
