module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs

open Silmaril.Machine.Lir (Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Label Prog State transfer)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Diamond (Val read)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires)

private theorem argumentPort_index (scope : Nat) (i : Fin scope) :
    (argumentPort scope i).index = i.val := by
  induction scope with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      change (argumentPort n i).index + 1 = i.val + 1
      rw [ih]

theorem checkColumn_registers {scope arity : Nat} {indices : List Nat}
    {wires : ArgumentColumn scope arity} (ok : checkColumn scope arity indices = some wires) :
    emitColumn wires = indices.map Reg.arg := by
  induction arity generalizing indices with
  | zero =>
    cases indices with
    | nil =>
      obtain rfl := Option.some.inj ok
      rfl
    | cons _ _ => cases ok
  | succ arity ih =>
    cases indices with
    | nil => cases ok
    | cons index rest =>
      unfold checkColumn at ok
      split at ok
      · rename_i valid
        cases tailEq : checkColumn scope arity rest with
        | none => simp [tailEq] at ok
        | some tail =>
          rw [tailEq] at ok
          obtain rfl := Option.some.inj ok
          change Reg.arg (argumentPort scope ⟨index, valid⟩).index :: emitColumn tail =
            Reg.arg index :: rest.map Reg.arg
          rw [argumentPort_index, ih tailEq]
      · cases ok

theorem readColumnWith_eq {args : List PortTy} {past : List (List PortTy)} {arity : Nat}
    (resolve : Silmaril.SSA.RVSDG.Address → Reg) (wires : Wires args past (wordPorts arity)) (input : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) (fr : Frame Reg)
    (agree : ∀ wire : Origin args past wordPort,
      fr.get (resolve wire.address) = some (read model wire input locals)) :
    fr.readAll (wires.addresses.map resolve) = some (words (wires.read input locals)) := by
  induction arity with
  | zero => cases wires; rfl
  | succ arity ih =>
    cases wires with
    | cons wire rest =>
      simp only [Wires.addresses, List.map_cons, Frame.readAll, List.mapM_cons,
        agree]
      have tail := ih rest
      unfold Frame.readAll at tail
      rw [tail]
      rfl

theorem readColumn_eq {args : List PortTy} {past : List (List PortTy)} {arity : Nat}
    (wires : Wires args past (wordPorts arity)) (input : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) (fr : Frame Reg)
    (agree : ∀ wire : Origin args past wordPort,
      fr.get (register wire.address) = some (read model wire input locals)) :
    fr.readAll (emitColumn wires) = some (words (wires.read input locals)) :=
  readColumnWith_eq register wires input locals fr agree

private theorem words_length {arity : Nat} (values : WordTuple arity) : (words values).length = arity := by
  induction arity with
  | zero => cases values; rfl
  | succ arity ih =>
    cases values with
    | cons value rest =>
      change (words rest).length + 1 = arity + 1
      rw [ih]

private theorem writeAll_exists (fr : Frame Reg) (regs : List Reg) (values : List Word)
    (h : regs.length = values.length) : ∃ after, fr.writeAll regs values = some after := by
  induction regs generalizing fr values with
  | nil => cases values <;> simp_all [Frame.writeAll]
  | cons reg rest ih =>
    cases values with
    | nil => simp at h
    | cons value restValues =>
      exact ih (fr.set reg value) restValues (Nat.succ.inj h)

theorem transfer_column {args : List PortTy} {past : List (List PortTy)} {arity : Nat}
    (wires : Wires args past (wordPorts arity)) (input : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) (p : Prog Reg) (s : State Reg)
    (target : Label) (block : Block Reg) (found : p.block? s.point.func target = some block)
    (arityEq : block.params.length = arity)
    (agree : ∀ wire : Origin args past wordPort,
      s.frame.get (register wire.address) = some (read model wire input locals)) :
    ∃ after, s.frame.writeAll block.params (words (wires.read input locals)) = some after ∧
      transfer p s target (emitColumn wires) =
        .running ⟨⟨s.point.func, target, 0⟩, after, s.stack, s.mem⟩ := by
  obtain ⟨after, wrote⟩ := writeAll_exists s.frame block.params _ (arityEq.trans (words_length _).symm)
  exact ⟨after, wrote, by simp [transfer, readColumn_eq wires input locals s.frame agree, found, wrote]⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs
