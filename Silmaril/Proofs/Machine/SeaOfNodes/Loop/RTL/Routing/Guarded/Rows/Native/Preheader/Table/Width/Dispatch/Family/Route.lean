module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Proofs

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Diamond (Val read)
open Silmaril.SSA.RVSDG (Tuple Locals extend)

variable {captures bank tests : Nat} {entrySigs sigs : List (List PortTy)}

theorem chain_block (p : Source captures bank entrySigs sigs tests) (i : Nat) :
    (lowerRTL p).block? 0 (3 + i) = (p.rows.blocks 3)[i]? := by
  change ([Width.preheader p.primary, header p, exitBlock] ++ p.rows.blocks 3)[3 + i]? = _
  rw [List.getElem?_append_right (by simp)]
  change (p.rows.blocks 3)[3 + i - 3]? = _
  rw [show 3 + i - 3 = i by omega]

theorem append_paths {prog : Prog Reg} {n k : Nat} {start middle finish : State Reg}
    (first : StepsNWithin prog [] n start middle) (rest : StepsNWithin prog [] k middle finish) :
    StepsNWithin prog [] (n + k) start finish := by
  induction first with
  | refl => simpa only [Nat.zero_add] using rest
  | head next _ ih => rw [Nat.succ_add]; exact .head next (ih rest)

theorem route (rows : Choices captures bank sigs tests) (prog : Prog Reg) (first : Nat)
    (found : ∀ i : Nat, prog.block? 0 (first + i) = (rows.blocks first)[i]?)
    (target : ∃ b, prog.block? 0 1 = some b ∧ b.params = paramRegs captures bank)
    (args : Tuple (Val model.value) (wordPorts captures ++ wordPorts bank))
    (locals : Locals (Val model.value) (extend [] sigs)) (fr : Frame Reg) (mem : Memory)
    (reads : ∀ origin : HeaderWord captures bank sigs,
      fr.get (register origin.address) = some (read model origin args locals)) :
    let slot := rows.select (fun origin => read model origin args locals)
    let column := rows.column slot
    let values := column.read args locals
    ∃ b, StepsNWithin prog [] slot.val ⟨⟨0, first, 0⟩, fr, [], mem⟩
      ⟨⟨0, first + slot.val, 0⟩, fr, [], mem⟩ ∧
      Fallthrough prog first slot.val fr mem ∧
      prog.block? 0 (first + slot.val) = some b ∧
      b.term.args[0]? = some (1, emitColumn column) ∧
      fr.readAll (emitColumn column) = some (words values) ∧
      step prog ⟨⟨0, first + slot.val, 0⟩, fr, [], mem⟩ =
        .running ⟨⟨0, 1, 0⟩, bindWords captures fr values, [], mem⟩ := by
  have latch (column : Feedback captures bank sigs) (label : Nat) :
      transfer prog ⟨⟨0, label, 0⟩, fr, [], mem⟩ 1 (emitColumn column) =
        .running ⟨⟨0, 1, 0⟩, bindWords captures fr (column.read args locals), [], mem⟩ := by
    obtain ⟨header, atHeader, params⟩ := target
    simp only [transfer, readColumn_eq column args locals fr reads, atHeader, params, bindWords_write]
  induction rows generalizing first with
  | last column =>
    let block : Block Reg := ⟨[], [], .jump 1 (emitColumn column)⟩
    have here : prog.block? 0 first = some block := by
      have h := found 0
      rw [Nat.add_zero] at h
      exact h
    have fetched : prog.fetch ⟨0, first, 0⟩ = some (.term block.term) := Prog.fetch_term here
    simp only [Choices.select, Choices.column, Fin.val_zero, Nat.add_zero]
    refine ⟨block, .refl, fun offset bound => (Nat.not_lt_zero offset bound).elim, here, rfl, readColumn_eq column args locals fr reads, ?_⟩
    simpa only [step, fetched, block] using latch column first
  | @test n selector column tail ih =>
    let block : Block Reg := ⟨[], [], .cond (register selector.address) 1 (emitColumn column) (first + 1) []⟩
    have here : prog.block? 0 first = some block := by
      have h := found 0
      rw [Nat.add_zero] at h
      exact h
    have fetched : prog.fetch ⟨0, first, 0⟩ = some (.term block.term) := Prog.fetch_term here
    let value : Word := read model selector args locals
    have fromFrame : fr.get (register selector.address) = some value := reads selector
    by_cases zero : value = 0
    · have later (i : Nat) : prog.block? 0 (first + 1 + i) = (tail.blocks (first + 1))[i]? := by
        rw [show first + 1 + i = first + (i + 1) by omega]
        exact found (i + 1)
      have nextFound : prog.block? 0 (first + 1) = (tail.blocks (first + 1))[0]? := by
        simpa only [Nat.add_zero] using later 0
      have params (b : Block Reg) (hb : (tail.blocks (first + 1))[0]? = some b) : b.params = [] := by
        cases tail <;> cases Option.some.inj hb <;> rfl
      have enters : step prog ⟨⟨0, first, 0⟩, fr, [], mem⟩ =
          .running ⟨⟨0, first + 1, 0⟩, fr, [], mem⟩ := by
        cases tailFound : (tail.blocks (first + 1))[0]? with
        | none => cases tail <;> cases tailFound
        | some b =>
          have existsBlock := nextFound.trans tailFound
          simp only [step, fetched, block, fromFrame, zero, ite_true, transfer,
            show fr.readAll [] = some [] from rfl, existsBlock, params b tailFound, Frame.writeAll]
      have smaller := ih (first + 1) later
      dsimp only at smaller ⊢
      have selected : (Choices.test selector column tail).select (fun origin => read model origin args locals) =
          (tail.select (fun origin => read model origin args locals)).succ := by
        change (if value = 0 then _ else _) = _
        rw [ite_eq_left zero]
      rw [selected]
      obtain ⟨b, path, falls, hb, operand, packet, transfer⟩ := smaller
      have address : first + (tail.select (fun origin => read model origin args locals)).succ.val =
          first + 1 + (tail.select (fun origin => read model origin args locals)).val := by
        simp only [Fin.val_succ]
        omega
      rw [address]
      refine ⟨b, .head ⟨enters, List.nil_suffix⟩ path, ?_, hb, operand, packet, transfer⟩
      intro offset bound
      cases offset with
      | zero => simpa only [Nat.add_zero] using enters
      | succ offset =>
        have inside : offset < (tail.select (fun origin => read model origin args locals)).val := by
          simp only [Fin.val_succ] at bound
          omega
        simpa only [show first + (offset + 1) = first + 1 + offset by omega] using falls offset inside
    · dsimp only
      have selected : (Choices.test selector column tail).select (fun origin => read model origin args locals) = 0 := by
        change (if value = 0 then _ else _) = _
        rw [ite_eq_right zero]
      rw [selected]
      have columnZero : (Choices.test selector column tail).column 0 = column := rfl
      rw [columnZero, Fin.val_zero, Nat.add_zero]
      refine ⟨block, .refl, fun offset bound => (Nat.not_lt_zero offset bound).elim, here, rfl, readColumn_eq column args locals fr reads, ?_⟩
      simpa only [step, fetched, block, fromFrame, ite_eq_right zero] using latch column first

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Proofs
